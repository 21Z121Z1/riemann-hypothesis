import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0058
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0039
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.TopLimitModules.LimJMemSmulTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsLocalRingOfAug
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve

namespace GlobalTheory.StalkJet

variable {k : Type} [Field k]

theorem isLocalRing_of_aug {A : Type} [CommRing A] [Algebra k A] (aug : A →ₐ[k] k) {n : ℕ}
    (h : RingHom.ker aug ^ n = ⊥) : IsLocalRing A := by
  haveI : Nontrivial A := (aug : A →+* k).domain_nontrivial
  have nil : ∀ a : A, aug a = 0 → IsNilpotent a := fun a ha =>
    ⟨n, by rw [← Ideal.mem_bot, ← h]; exact Ideal.pow_mem_pow ha n⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : aug a = 0
  · exact Or.inr (nil a ha).isUnit_one_sub
  · left
    have h1 : IsNilpotent (a - algebraMap k A (aug a)) := nil _ (by simp)
    have h2 : IsUnit (algebraMap k A (aug a)) := (IsUnit.mk0 _ ha).map _
    have := h1.isUnit_add_right_of_commute h2 (Commute.all _ _)
    simpa using this

theorem exists_factor {B : Over (Sp k)} (b : B.left) [Algebra k (B.left.presheaf.stalk b)]
    (hb : B.left.fromSpecStalk b ≫ B.hom = spMap (algebraMap k (B.left.presheaf.stalk b)))
    {A : Type} [CommRing A] [Algebra k A] [IsLocalRing A] (y : algOver k A ⟶ B)
    (hy : y.left (closedPoint A) = b) :
    ∃ τ : B.left.presheaf.stalk b →ₐ[k] A, IsLocalHom τ ∧
      spMap (τ : B.left.presheaf.stalk b →+* A) ≫ B.left.fromSpecStalk b = y.left := by
  subst hy
  have e := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of A) y.left
  have w : y.left ≫ B.hom = spMap (algebraMap k A) := Over.w y
  have e2 : CommRingCat.ofHom (algebraMap k (B.left.presheaf.stalk (y.left (closedPoint A)))) ≫
      Scheme.stalkClosedPointTo (R := .of A) y.left = CommRingCat.ofHom (algebraMap k A) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    refine Eq.trans ?_ w
    exact (congrArg (Spec.map (Scheme.stalkClosedPointTo (R := .of A) y.left) ≫ ·) hb.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ B.hom) e))
  refine ⟨⟨(Scheme.stalkClosedPointTo (R := .of A) y.left).hom, fun c => ?_⟩, ?_, e⟩
  · exact congrArg (fun q => q.hom c) e2
  · exact ⟨(Scheme.isLocalHom_stalkClosedPointTo' (R := A) y.left).1⟩

theorem jet_of_mono {B : Over (Sp k)} [GrpObj B] [Smooth B.hom] {κ : Type} {m : ℕ}
    (x : algOver k (JetR k κ m) ⟶ B) (h0 : algOverHom (jetZeroR k κ m) ≫ x = 1)
    (hu : ∀ (κ' : Type) (y : algOver k (JetR k κ' m) ⟶ B), algOverHom (jetZeroR k κ' m) ≫ y = 1 →
      ∃! ψ : JetR k κ m →ₐ[k] JetR k κ' m, (∀ j, jetZeroR k κ' m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ x)
    {O : Type} [CommRing O] [Algebra k O] (s : algOver k O ⟶ B) [Mono s.left]
    (ε : O →ₐ[k] k) (hε : algOverHom ε ≫ s = 1) (τ : O →ₐ[k] JetR k κ m) (hτ : algOverHom τ ≫ s = x) :
    Function.Surjective τ ∧ ∀ a, τ a = 0 ↔ a ∈ RingHom.ker ε ^ (m + 1) := by
  have canc : ∀ {A : Type} [CommRing A] [Algebra k A] (f f' : O →ₐ[k] A),
      algOverHom f ≫ s = algOverHom f' ≫ s → f = f' := by
    intro A _ _ f f' h
    have h1 : (algOverHom f).left ≫ s.left = (algOverHom f').left ≫ s.left := congrArg (·.left) h
    have h2 : spMap (f : O →+* A) = spMap (f' : O →+* A) := (cancel_mono s.left).1 h1
    have h3 := Spec.map_injective h2
    ext a
    exact congrArg (fun q => q.hom a) h3
  let aJ : JetR k κ m →ₐ[k] k := Chart.jetAug k κ m
  have hJ : RingHom.ker aJ ^ (m + 1) = ⊥ := Chart.ker_jetAug_pow κ m
  have hxa : algOverHom aJ ≫ x = 1 := by
    have : aJ = (Chart.jetAug k κ 0).comp (jetZeroR k κ m) := GlobalTheory.ChartUniv.jetAug_eq κ m
    rw [this, ← algOverHom_comp, Category.assoc, h0, MonObj.comp_one]
  have haug : aJ.comp τ = ε := canc _ _ (by rw [← algOverHom_comp, Category.assoc, hτ, hxa, hε])
  set I : Ideal O := RingHom.ker ε ^ (m + 1) with hI
  have hkill : ∀ a ∈ I, τ a = 0 := by
    intro a ha
    have hle : RingHom.ker ε ≤ (RingHom.ker aJ).comap τ := fun c hc => by
      show aJ (τ c) = 0
      rw [← AlgHom.comp_apply, haug]; exact hc
    have h2 := Ideal.le_comap_pow τ (m + 1) (Ideal.pow_right_mono hle (m + 1) ha)
    rw [hJ] at h2
    simpa using h2
  have hε0 : ∀ a ∈ I, ε a = 0 := fun a ha => Ideal.pow_le_self (Nat.succ_ne_zero m) ha
  let aA : (O ⧸ I) →ₐ[k] k := Ideal.Quotient.liftₐ I ε hε0
  have haA : aA.comp (Ideal.Quotient.mkₐ k I) = ε := by ext a; rfl
  have hA : RingHom.ker aA ^ (m + 1) = ⊥ := by
    have hle : RingHom.ker aA ≤ (RingHom.ker ε).map (Ideal.Quotient.mk I) := by
      intro c hc
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact Ideal.mem_map_of_mem _ hc
    rw [← le_bot_iff]
    refine (Ideal.pow_right_mono hle _).trans ?_
    rw [← Ideal.map_pow, ← hI, Ideal.map_quotient_self]
  obtain ⟨ψ, ⟨h1, h2⟩, -⟩ := GlobalTheory.ChartUniv.univ_all (G := B) x h0 hu (O ⧸ I) aA hA
    (algOverHom (Ideal.Quotient.mkₐ k I) ≫ s) (by
      show algOverHom aA ≫ algOverHom (Ideal.Quotient.mkₐ k I) ≫ s = 1
      rw [← Category.assoc, algOverHom_comp, haA, hε])
  have h1' : aA.comp ψ = aJ := h1
  have h2' : algOverHom (Ideal.Quotient.mkₐ k I) ≫ s = algOverHom ψ ≫ x := h2
  have hψτ : ψ.comp τ = Ideal.Quotient.mkₐ k I :=
    canc _ _ (by rw [← algOverHom_comp, Category.assoc, hτ, h2'])
  let τ' : (O ⧸ I) →ₐ[k] JetR k κ m := Ideal.Quotient.liftₐ I τ hkill
  have hτ' : τ'.comp (Ideal.Quotient.mkₐ k I) = τ := by ext a; rfl
  have haτ' : aJ.comp τ' = aA := by
    refine Ideal.Quotient.algHom_ext k ?_
    rw [AlgHom.comp_assoc, hτ', haug, haA]
  have hid : τ'.comp ψ = AlgHom.id k _ := by
    refine (GlobalTheory.ChartUniv.univ_all (G := B) x h0 hu (JetR k κ m) aJ hJ x hxa).unique ⟨?_, ?_⟩ ⟨rfl, ?_⟩
    · show aJ.comp (τ'.comp ψ) = aJ
      rw [← AlgHom.comp_assoc, haτ', h1']
    · show x = algOverHom (τ'.comp ψ) ≫ x
      rw [← algOverHom_comp, Category.assoc, ← h2', ← Category.assoc, algOverHom_comp, hτ', hτ]
    · show x = algOverHom (AlgHom.id k _) ≫ x
      rw [algOverHom_id, Category.id_comp]
  refine ⟨fun c => ?_, fun a => ⟨fun ha => ?_, hkill a⟩⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ c)
    refine ⟨a, ?_⟩
    have := AlgHom.congr_fun hid c
    rw [AlgHom.comp_apply, ← ha] at this
    exact this
  · have := AlgHom.congr_fun hψτ a
    rw [AlgHom.comp_apply, ha, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm

theorem stalk_jet : ∀ (k : Type) [Field k] (B : Over (Sp k)) [GrpObj B] [IsCommMonObj B], Smooth B.hom → ∀ (g : ℕ) (F : FGLaw k g) (x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin g) m) ⟶ B), IsChartJ B F x → ∀ (b : B.left), b = η[B].left (closedPoint k) → ∀ [Algebra k (B.left.presheaf.stalk b)], B.left.fromSpecStalk b ≫ B.hom = spMap (algebraMap k (B.left.presheaf.stalk b)) → ∀ m : ℕ, ∃ τ : B.left.presheaf.stalk b →ₐ[k] JetR k (Fin 1 × Fin g) m, spMap (τ : B.left.presheaf.stalk b →+* JetR k (Fin 1 × Fin g) m) ≫ B.left.fromSpecStalk b = (x m).left ∧ Function.Surjective τ ∧ ∀ a, τ a = 0 ↔ a ∈ maximalIdeal (B.left.presheaf.stalk b) ^ (m + 1) := by
  intro k _ B _ _ hB g F x hx b hb _ hs m
  haveI := hB
  let aJ : JetR k (Fin 1 × Fin g) m →ₐ[k] k := Chart.jetAug k _ m
  have hJ : RingHom.ker aJ ^ (m + 1) = ⊥ := Chart.ker_jetAug_pow _ m
  haveI := isLocalRing_of_aug aJ hJ
  have h0 : algOverHom (jetZeroR k _ m) ≫ x m = 1 := hx.zero m
  have hxa : algOverHom aJ ≫ x m = 1 := by
    have : aJ = (Chart.jetAug k _ 0).comp (jetZeroR k _ m) := GlobalTheory.ChartUniv.jetAug_eq _ m
    rw [this, ← algOverHom_comp, Category.assoc, h0, MonObj.comp_one]
  have he : (1 : algOver k k ⟶ B).left (closedPoint k) = b := by
    rw [hb]
    show η[B].left ((toUnit (algOver k k)).left (closedPoint k)) = _
    exact congrArg η[B].left (Subsingleton.elim (α := PrimeSpectrum k) _ _)
  have hxb : (x m).left (closedPoint _) = b := by
    haveI : IsLocalHom (aJ : JetR k (Fin 1 × Fin g) m →+* k) :=
      IsLocalHom.of_surjective _ (fun c => ⟨algebraMap _ _ c, aJ.commutes c⟩)
    rw [← he, ← hxa, ← IsLocalRing.comap_closedPoint (aJ : JetR k (Fin 1 × Fin g) m →+* k)]
    rfl
  obtain ⟨ε, hεl, hε⟩ := exists_factor b hs (1 : algOver k k ⟶ B) he
  obtain ⟨τ, -, hτ⟩ := exists_factor b hs (x m) hxb
  let s : algOver k (B.left.presheaf.stalk b) ⟶ B := Over.homMk (B.left.fromSpecStalk b) hs
  haveI : Mono s.left := inferInstanceAs (Mono (B.left.fromSpecStalk b))
  have hker : RingHom.ker ε = maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ε (fun c => ⟨algebraMap _ _ c, ε.commutes c⟩))
  have := jet_of_mono (x m) h0 (fun κ' => hx.univ κ' m) s ε (Over.OverMorphism.ext hε) τ (Over.OverMorphism.ext hτ)
  rw [hker] at this
  exact ⟨τ, hτ, this⟩

end GlobalTheory.StalkJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowExponentPartMemGaugedCurveLogarithms
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

noncomputable section

namespace GlobalTheory.RowLaw.TypPart

variable {C : Type} [Field C]

theorem ge_intCast (V : VF C) (a : ℤ) : V.Ge 0 (a : C) := by
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · simpa using VF.ge_natCast (V := V) n
  · simpa using (VF.ge_natCast (V := V) n).neg

theorem v_prime_eq_zero (V : VF C) {p : ℕ} (hp : p.Prime) (hpl : p ≠ V.l) : V.v (p : C) = 0 := by
  have hc : IsCoprime (p : ℤ) (V.l : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp V.l_prime).2 hpl)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : C) * (p : C) + (b : C) * (V.l : C) = 1 := by
    have := congrArg (fun z : ℤ => (z : C)) hab
    simpa using this
  have h0 : (0 : WithTop ℝ) ≤ V.v (p : C) := by simpa [VF.Ge] using VF.ge_natCast (V := V) p
  have ha : (0 : WithTop ℝ) ≤ V.v (a : C) := by simpa [VF.Ge] using ge_intCast V a
  have hb : (0 : WithTop ℝ) ≤ V.v (b : C) := by simpa [VF.Ge] using ge_intCast V b
  by_contra hne
  have hpos : (0 : WithTop ℝ) < V.v (p : C) := lt_of_le_of_ne h0 (Ne.symm hne)
  have e1 : (0 : WithTop ℝ) < V.v ((a : C) * (p : C)) := by
    rw [V.v.map_mul]; exact lt_of_lt_of_le hpos (le_add_of_nonneg_left ha)
  have e2 : (0 : WithTop ℝ) < V.v ((b : C) * (V.l : C)) := by
    rw [V.v.map_mul, V.v_l]; exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hb)
  have := V.v.map_lt_add e1 e2
  rw [h1, V.v.map_one] at this
  exact lt_irrefl _ this

theorem ge_of_pow_eq_one (V : VF C) {ζ : C} {p : ℕ} (hp : 0 < p) (h : ζ ^ p = 1) : V.Ge 0 ζ := by
  have h1 : p • V.v ζ = 0 := by rw [← V.v.map_pow, h, V.v.map_one]
  unfold VF.Ge
  induction hv : V.v ζ using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hv, ← WithTop.coe_nsmul] at h1
    have h2 : p • t = 0 := by exact_mod_cast h1
    have h3 : t = 0 := by
      rw [nsmul_eq_mul] at h2
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd (by exact_mod_cast h) hp.ne'
      · exact h
    rw [h3]

theorem sum_pow_root {ζ : C} {p : ℕ} (hζ : IsPrimitiveRoot ζ p) (m : ℕ) :
    ∑ j ∈ Finset.range p, (ζ ^ j) ^ m = if p ∣ m then (p : C) else 0 := by
  have e : ∀ j, (ζ ^ j) ^ m = (ζ ^ m) ^ j := fun j => by rw [← pow_mul, ← pow_mul, mul_comm]
  simp_rw [e]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]; simp
  · have hne : ζ ^ m - 1 ≠ 0 := fun h' => h ((hζ.pow_eq_one_iff_dvd m).1 (sub_eq_zero.1 h'))
    have := geom_sum_mul (ζ ^ m) p
    rw [← pow_mul, mul_comm m p, pow_mul, hζ.pow_eq_one, one_pow, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hne

open Classical in

def filt (P : ℕ → Prop) (f : PowerSeries C) : PowerSeries C :=
  PowerSeries.mk fun m => if P m then PowerSeries.coeff m f else 0

open Classical in
theorem coeff_filt (P : ℕ → Prop) (f : PowerSeries C) (m : ℕ) :
    PowerSeries.coeff m (filt P f) = if P m then PowerSeries.coeff m f else 0 := by
  simp [filt]

theorem sub_avg [CharZero C] {ζ : C} {p : ℕ} (hp : 0 < p) (hζ : IsPrimitiveRoot ζ p) (f : PowerSeries C) :
    f + -((p : C)⁻¹ • ∑ j ∈ Finset.range p, PowerSeries.rescale (ζ ^ j) f) = filt (fun m => ¬ p ∣ m) f := by
  ext m
  have hp' : (p : C) ≠ 0 := by exact_mod_cast hp.ne'
  rw [coeff_filt, map_add, map_neg, PowerSeries.coeff_smul, map_sum]
  simp_rw [PowerSeries.coeff_rescale]
  rw [← Finset.sum_mul, sum_pow_root hζ]
  by_cases h : p ∣ m
  · simp [h, hp']
  · simp [h]

theorem filt_filt (P Q : ℕ → Prop) (f : PowerSeries C) :
    filt P (filt Q f) = filt (fun m => P m ∧ Q m) f := by
  ext m
  rw [coeff_filt, coeff_filt, coeff_filt]
  by_cases h : P m <;> by_cases h' : Q m <;> simp [h, h']

theorem filt_congr {P Q : ℕ → Prop} (h : ∀ m, P m ↔ Q m) (f : PowerSeries C) : filt P f = filt Q f := by
  have : P = Q := funext fun m => propext (h m)
  rw [this]

theorem filt_true {P : ℕ → Prop} (h : ∀ m, P m) (f : PowerSeries C) : filt P f = f := by
  ext m
  rw [coeff_filt, if_pos (h m)]

def Good (l n m : ℕ) : Prop := ∀ p < n, p.Prime → p ≠ l → ¬ p ∣ m

theorem coeff_filt_good {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (f : PowerSeries C) (m n : ℕ) (hn : m + 3 ≤ n) :
    PowerSeries.coeff m (filt (Good l n) f) = PowerSeries.coeff m (typ l f) := by
  rw [coeff_filt]
  unfold typ
  by_cases hm : ∃ s, l ^ s = m
  · obtain ⟨s, rfl⟩ := hm
    rw [coeff_tyS_pow hl.two_le, if_pos]
    intro p _ hp hpl hd
    exact hpl ((Nat.prime_dvd_prime_iff_eq hp hl).1 (hp.dvd_of_dvd_pow hd))
  · rw [coeff_tyS_of_ne _ m (fun s hs => hm ⟨s, hs⟩), if_neg]
    intro hg
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact hg 2 (by omega) Nat.prime_two (Ne.symm hl2) (dvd_zero 2)
    · apply hm
      refine ⟨_, (Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne' ?_).symm⟩
      intro q hq hqm
      by_contra hne
      exact hg q (by have := Nat.le_of_dvd hpos hqm; omega) hq hne hqm

variable {V : VF C} {d : ℕ} [NeZero d] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {X : RawChart C d I κ}

theorem filt_not_dvd_mem (hX : RLaw X V) (g : Fin 2) {p : ℕ} (hp : p.Prime) (hpl : p ≠ V.l)
    (a : (κ → PowerSeries C) × (JJ I g → PowerSeries C)) (ha : a ∈ Cv X V g) :
    ((fun i => filt (fun m => ¬ p ∣ m) (a.1 i), fun q => filt (fun m => ¬ p ∣ m) (a.2 q)) :
      (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g := by
  have := hX.charZero
  have := hX.closed
  have : NeZero (p : C) := ⟨by exact_mod_cast hp.ne_zero⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  obtain ⟨h0, hadd, hneg, hres⟩ := GlobalTheory.T.gaugedFormalGroupCurveLogarithms_addSubgroup_rescale C V d I κ X hX g
  have hζ0 : V.Ge 0 ζ := ge_of_pow_eq_one V hp.pos hζ.pow_eq_one
  have hs : ∀ n : ℕ, ((fun i => ∑ j ∈ Finset.range n, PowerSeries.rescale (ζ ^ j) (a.1 i),
      fun q => ∑ j ∈ Finset.range n, PowerSeries.rescale (ζ ^ j) (a.2 q)) :
      (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact h0
    | succ n ih =>
      have := hadd _ ih _ (hres (ζ ^ n) (hζ0.pow n) a ha)
      simp only [Finset.sum_range_succ]
      exact this
  have h2 := hadd _ ha _ (hneg _ (GlobalTheory.T.curveLogarithms_inv_natCast_smul_mem C V d I κ X hX g p (v_prime_eq_zero V hp hpl) _ (hs p)))
  convert h2 using 1
  refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
  · exact (sub_avg hp.pos hζ (a.1 i)).symm
  · exact (sub_avg hp.pos hζ (a.2 q)).symm

theorem filt_good_mem (hX : RLaw X V) (g : Fin 2)
    (a : (κ → PowerSeries C) × (JJ I g → PowerSeries C)) (ha : a ∈ Cv X V g) (n : ℕ) :
    ((fun i => filt (Good V.l n) (a.1 i), fun q => filt (Good V.l n) (a.2 q)) :
      (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g := by
  induction n with
  | zero =>
    have h : ∀ m, Good V.l 0 m := fun m p hp => absurd hp (Nat.not_lt_zero p)
    simp only [filt_true h]
    exact ha
  | succ n ih =>
    by_cases hn : n.Prime ∧ n ≠ V.l
    · have h : ∀ m, Good V.l (n + 1) m ↔ (¬ n ∣ m ∧ Good V.l n m) := by
        intro m
        constructor
        · intro hg
          exact ⟨hg n (by omega) hn.1 hn.2, fun p hp => hg p (by omega)⟩
        · rintro ⟨h1, h2⟩ p hp hpp hpl
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with h | rfl
          · exact h2 p h hpp hpl
          · exact h1
      have := filt_not_dvd_mem hX g hn.1 hn.2 _ ih
      simp only [filt_filt] at this
      simp only [filt_congr h]
      exact this
    · have h : ∀ m, Good V.l (n + 1) m ↔ Good V.l n m := by
        intro m
        constructor
        · intro hg p hp
          exact hg p (by omega)
        · intro h2 p hp hpp hpl
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with h | rfl
          · exact h2 p h hpp hpl
          · exact absurd ⟨hpp, hpl⟩ hn
      simp only [filt_congr h]
      exact ih

end GlobalTheory.RowLaw.TypPart

open GlobalTheory.RowLaw.TypPart in

theorem GlobalTheory.RowLaw.typ_mem_Cv : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, ∀ a ∈ Cv X V g, ((fun i => typ V.l (a.1 i), fun q => typ V.l (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X hX g a ha
  refine GlobalTheory.RowLaw.cv_closed_under_limits C V d I κ X hX g _ _ (filt_good_mem hX g a ha) fun m => ⟨m + 3, fun n hn => ⟨fun i => ?_, fun q => ?_⟩⟩
  · exact coeff_filt_good V.l_prime hX.odd _ m n hn
  · exact coeff_filt_good V.l_prime hX.odd _ m n hn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TjEqZeroIff
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve
open ReciprocityTheory.ChartRestriction.G.Pdiv.TL

namespace GlobalTheory.JetExpansion

variable {k : Type} [CommRing k] {κ : Type} [Finite κ]

def tj (m : ℕ) : MvPowerSeries κ k →ₐ[k] JetR k κ m :=
  (MvPowerSeries.truncTotalAlgHom κ k (m + 1)).restrictScalars k

theorem tj_eq_iff (m : ℕ) (f g : MvPowerSeries κ k) :
    tj m f = tj m g ↔ ∀ x : κ →₀ ℕ, x.degree < m + 1 → MvPowerSeries.coeff x f = MvPowerSeries.coeff x g :=
  limJ_tt_eq_iff m f g

theorem tj_ext {f g : MvPowerSeries κ k} (h : ∀ m, tj m f = tj m g) : f = g := by
  ext x
  exact (tj_eq_iff x.degree f g).1 (h _) x (Nat.lt_succ_self _)

theorem tj_eq_zero_iff (m : ℕ) (f : MvPowerSeries κ k) :
    tj m f = 0 ↔ f ∈ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ k)) ^ (m + 1) := by
  rw [← GlobalTheory.germIdeal_eq_span, GlobalTheory.mem_germIdeal_pow_iff, ← map_zero (tj (k := k) (κ := κ) m), tj_eq_iff]
  simp only [map_zero]

theorem exists_tj (p : ∀ m, JetR k κ m) (hp : ∀ m, jetTruncR k κ m (p (m + 1)) = p m) :
    ∃ f : MvPowerSeries κ k, ∀ m, tj m f = p m := by
  choose P hP using fun m => Ideal.Quotient.mk_surjective (p m)
  have hck : ∀ (u : κ →₀ ℕ) m, u.degree ≤ m → (P m).coeff u = (P u.degree).coeff u := by
    intro u m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      rw [← ih]
      have h1 : (Ideal.Quotient.mk _ (P m) : JetR k κ m) = Ideal.Quotient.mk _ (P (m + 1)) := by
        rw [hP, ← hp m, ← hP]
        rfl
      exact ((limJ_mk_eq_iff m _ _).1 h1 u (by omega)).symm
  refine ⟨fun u => (P u.degree).coeff u, fun m => ?_⟩
  rw [← hP m]
  refine (limJ_mk_eq_iff m (MvPowerSeries.truncTotal (m + 1) _) _).2 fun u hu => ?_
  exact (MvPowerSeries.coeff_truncTotal _ hu).trans (hck u m (by omega)).symm

theorem exists_expansion : ∀ (k : Type) [CommRing k] (g : ℕ), 0 < g → ∀ (A : Type) [CommRing A] [Algebra k A] (I : Ideal A) (τ : ∀ m : ℕ, A →ₐ[k] JetR k (Fin 1 × Fin g) m), (∀ m a, jetTruncR k _ m (τ (m + 1) a) = τ m a) → (∀ m, Function.Surjective (τ m)) → (∀ m a, τ m a = 0 ↔ a ∈ I ^ (m + 1)) → ∃ j : A →ₐ[k] PS k 1 g, (∀ (m : ℕ) (a : A), j a ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin g → PS k 1 g)) ^ m ↔ a ∈ I ^ m) ∧ (∀ (m : ℕ) (s : PS k 1 g), ∃ a : A, j a - s ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin g → PS k 1 g)) ^ m) ∧ ∀ (a : A) (s : PS k 1 g), (∀ m, τ m a = psJet m s) → j a = s := by
  intro k _ g hg A _ _ I τ hc hs hk
  choose F hF using fun a : A => exists_tj (fun m => τ m a) (fun m => hc m a)
  let j : A →ₐ[k] PS k 1 g :=
    { toFun := F
      map_one' := tj_ext fun m => by rw [hF, map_one, map_one]
      map_mul' := fun a b => tj_ext fun m => by rw [map_mul, hF, hF, hF, map_mul]
      map_zero' := tj_ext fun m => by rw [hF, map_zero, map_zero]
      map_add' := fun a b => tj_ext fun m => by rw [map_add, hF, hF, hF, map_add]
      commutes' := fun r => tj_ext fun m => by rw [hF, AlgHom.commutes, AlgHom.commutes] }
  have hj : ∀ m a, tj m (j a) = τ m a := fun m a => hF a m
  refine ⟨j, fun m a => ?_, fun m s => ?_, fun a s h => ?_⟩
  · rcases m with _ | m
    · simp
    · rw [← tj_eq_zero_iff, hj, hk]
  · obtain ⟨a, ha⟩ := hs m (tj m s)
    refine ⟨a, Ideal.pow_le_pow_right (Nat.le_succ m) ?_⟩
    rw [← tj_eq_zero_iff, map_sub, hj, ha, sub_self]
  · refine tj_ext fun m => ?_
    rw [hj, h, limJ_psJet_eq Nat.one_pos hg]
    rfl

end GlobalTheory.JetExpansion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TorusPointRelationSuccThickening
section
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

theorem iRel_succ : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) (k : ℕ) (S : Type) [CommRing S] [Algebra R S] χ z, IRel (U.gt k) S χ z → IRel (U.gt (k + 1)) S χ z := by
  rintro R _ _ I D A G _ _ U k S _ _ χ z ⟨w, hw, hz⟩
  have t : Out.thickMap R I k G ≫ (Out.fstG I (k + 1) G).left = (Out.fstG I k G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  let Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) :=
    Over.mk (w ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.toPre.X).hom)
  let τ : Z ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.toPre.X := Over.homMk w rfl
  let r : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left := (τ ≫ (U.gt k).i).left
  have hr : r ≫ (Out.fstG I k G).left = z.left := (Category.assoc _ _ _).trans hz
  have c : r ≫ (U.gt k).pG.left = r ≫ (Out.fstG I k G).left ≫ G.hom ≫ eSec D.toPre.P.A :=
    (CharAgree.comp_q_eq_one_iff (U.gt k) (τ ≫ (U.gt k).i)).1 (by
      rw [Category.assoc, (U.gt k).isKernel.w, ← Category.assoc]
      exact congrArg (· ≫ _) (toUnit_unique _ _))
  let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (k + 1 + 1)))) :=
    Over.mk ((r ≫ Out.thickMap R I k G) ≫ (Out.thickObj R I (k + 1) G).hom)
  let a : Z' ⟶ Out.thickObj R I (k + 1) G := Over.homMk (r ≫ Out.thickMap R I k G) rfl
  have c' : a.left ≫ (U.gt (k + 1)).pG.left =
      a.left ≫ (Out.fstG I (k + 1) G).left ≫ G.hom ≫ eSec D.toPre.P.A := by
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (U.gt_q k)).trans (c.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ G.hom ≫ eSec D.toPre.P.A) t.symm).trans (Category.assoc _ _ _)
  let τ' := (U.gt (k + 1)).isKernel.lift a (toUnit _) ((CharAgree.comp_q_eq_one_iff (U.gt (k + 1)) a).2 c')
  have hτ : τ' ≫ (U.gt (k + 1)).i = a := (U.gt (k + 1)).isKernel.lift_fst _ _ _
  refine ⟨τ'.left, fun x => ?_, ?_⟩
  · refine Eq.trans (congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ?_) (hw x)
    apply TopCat.Presheaf.section_ext (Spec (CommRingCat.of S)).sheaf ⊤
    intro y hy
    choose J hJ using fun ψ : Spec (CommRingCat.of S) ⟶ D.toPre.P.A.left =>
      Geo.Tor.exists_chart D.toPre.P.isLB (ψ y)
    have k₀ := (TorusCoord.val_torus_point_and_translate R I D.toPre k G (U.gt k) Z τ 1 y J hJ x).1
    have k₁ := (TorusCoord.val_torus_point_and_translate R I D.toPre (k + 1) G (U.gt (k + 1)) Z' τ' 1 y J hJ x).1
    rw [hτ] at k₁
    have e := congrArg Units.val (k₁.symm.trans ((Geo.Tor.val_pull hJ _ (Out.thickMap R I k G) r).symm.trans
      ((Geo.Tor.val_corr hJ (U.gt_t k x) r).trans k₀)))
    exact (Geo.Tor.gm_val _ _ ⊤ trivial _).symm.trans (e.trans (Geo.Tor.gm_val _ _ ⊤ trivial _))
  · refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun φ => φ.left ≫ (Out.fstG I (k + 1) G).left) hτ).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) t).trans hr)

end GlobalTheory.ChF
end

