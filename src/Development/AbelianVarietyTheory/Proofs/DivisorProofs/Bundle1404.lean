import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1379
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.InertUQ

open IsDedekindDomain.HeightOneSpectrum

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem mem_max_iff (x : w.adicCompletionIntegers E) :
    x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) ↔ Valued.v (x : w.adicCompletion E) < 1 := by
  have hI := Valuation.valuationSubring.integers (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hx : Valued.v (x : w.adicCompletion E) ≤ 1 := x.2
  constructor
  · intro hn
    refine lt_of_le_of_ne hx fun h => hn ?_
    exact (hI.isUnit_iff_valuation_eq_one (x := x)).2 h
  · intro hlt hu
    exact (ne_of_lt hlt) ((hI.isUnit_iff_valuation_eq_one (x := x)).1 hu)

private lemma withZero_lt_one_iff_le_exp_neg_one (g : WithZero (Multiplicative ℤ)) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · rw [← WithZero.exp_log hg, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

private lemma mem_span_pow_iff_valuation_le_exp_neg_one_pow (p : w.adicCompletionIntegers E)
    (hp : Valued.v (p : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (a : w.adicCompletionIntegers E) :
    a ∈ Ideal.span {p ^ n} ↔ Valued.v (a : w.adicCompletion E) ≤ WithZero.exp (-1 : ℤ) ^ n := by
  have hp0 : (p : w.adicCompletion E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, rfl⟩
    have hb : Valued.v (b : w.adicCompletion E) ≤ 1 := b.2
    push_cast
    rw [map_mul, map_pow, hp]
    exact mul_le_of_le_one_right' hb
  · intro ha
    have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-1 : ℤ) ^ n :=
      zero_lt_iff.2 (pow_ne_zero _ WithZero.exp_ne_zero)
    have hb : Valued.v ((a : w.adicCompletion E) / (p : w.adicCompletion E) ^ n) ≤ 1 := by
      rw [map_div₀, map_pow, hp]
      exact (div_le_one₀ hpos).2 ha
    refine ⟨⟨_, hb⟩, ?_⟩
    apply Subtype.ext
    push_cast
    field_simp

private lemma maximalIdeal_eq_span_of_valuation_eq_exp_neg_one (p : w.adicCompletionIntegers E)
    (hp : Valued.v (p : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) = Ideal.span {p} := by
  ext a
  have h := mem_span_pow_iff_valuation_le_exp_neg_one_pow w p hp 1 a
  rw [pow_one, pow_one] at h
  rw [h, mem_max_iff, withZero_lt_one_iff_le_exp_neg_one]

theorem valuation_max_eq (ϖ : w.adicCompletion E) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (x : w.adicCompletion E) :
    (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation (w.adicCompletion E) x
      = Valued.v x := by
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ]
    exact ((withZero_lt_one_iff_le_exp_neg_one _).2 le_rfl).le
  let p : w.adicCompletionIntegers E := ⟨ϖ, hϖ1⟩
  have hp : Valued.v (p : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hp0 : p ≠ 0 := fun h => hϖ0 (congrArg Subtype.val h)
  have hVp : (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) ϖ = WithZero.exp (-1 : ℤ) := by
    have h1 := (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation_of_algebraMap
      (K := w.adicCompletion E) p
    rw [(IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).intValuation_singleton hp0
      (maximalIdeal_eq_span_of_valuation_eq_exp_neg_one w p hp)] at h1
    exact h1
  have hVu : ∀ a : w.adicCompletionIntegers E, Valued.v (a : w.adicCompletion E) = 1 →
      (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
        (w.adicCompletion E) a = 1 := by
    intro a ha
    have h1 := (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation_of_algebraMap
      (K := w.adicCompletion E) a
    refine h1.trans (HeightOneSpectrum.intValuation_eq_one_iff.2 fun hmem => ?_)
    have := (mem_max_iff w a).1 hmem
    rw [ha] at this
    exact lt_irrefl _ this
  by_cases hx : x = 0
  · simp [hx]
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v x = WithZero.exp k := ⟨_, (WithZero.exp_log hvx).symm⟩
  have hy : Valued.v (x * ϖ ^ k) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, hk, ← WithZero.exp_zsmul, ← WithZero.exp_add, WithZero.exp_eq_one]
    simp
  have hV : (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) (x * ϖ ^ k) = 1 := hVu ⟨x * ϖ ^ k, hy.le⟩ hy
  have hxe : x = (x * ϖ ^ k) * ϖ ^ (-k) := by
    rw [mul_assoc, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, mul_one]
  have e1 : (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) x = (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) (x * ϖ ^ k) * (IsDiscreteValuationRing.maximalIdeal
        (w.adicCompletionIntegers E)).valuation (w.adicCompletion E) ϖ ^ (-k) := by
    rw [← map_zpow₀, ← Valuation.map_mul, ← hxe]
  have e2 : Valued.v x = Valued.v (x * ϖ ^ k) * Valued.v ϖ ^ (-k) := by
    rw [← map_zpow₀, ← Valuation.map_mul, ← hxe]
  rw [e1, e2, hV, hVp, hy, hϖ]

private lemma isAdicComplete_maximalIdeal_adicCompletionIntegers (ϖ : w.adicCompletion E) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    IsAdicComplete (IsLocalRing.maximalIdeal (w.adicCompletionIntegers E))
      (w.adicCompletionIntegers E) := by
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ]
    exact ((withZero_lt_one_iff_le_exp_neg_one _).2 le_rfl).le
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  let p : w.adicCompletionIntegers E := ⟨ϖ, hϖ1⟩
  have hp : Valued.v (p : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := hϖ
  have hpow : ∀ (n : ℕ) (a : w.adicCompletionIntegers E),
      a ∈ (IsLocalRing.maximalIdeal (w.adicCompletionIntegers E)) ^ n ↔
        Valued.v (a : w.adicCompletion E) ≤ Valued.v ϖ ^ n := by
    intro n a
    rw [maximalIdeal_eq_span_of_valuation_eq_exp_neg_one w p hp, Ideal.span_singleton_pow, hϖ]
    exact mem_span_pow_iff_valuation_le_exp_neg_one_pow w p hp n a
  have hadic : IsAdic (IsLocalRing.maximalIdeal (w.adicCompletionIntegers E)) := by
    rw [isAdic_iff]
    constructor
    · intro n
      have hset : ((IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) ^ n : Ideal (w.adicCompletionIntegers E)) :
          Set (w.adicCompletionIntegers E)) =
          Subtype.val ⁻¹' {y : w.adicCompletion E |
            (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).restrict y ≤
              (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).restrict (ϖ ^ n)} := by
        ext a
        simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_ofPred_eq]
        rw [Valuation.restrict_le_iff, map_pow]
        exact hpow n a
      rw [hset]
      refine (Valued.isOpen_closedBall _ ?_).preimage continuous_subtype_val
      intro h0
      have h1 : Valued.v (ϖ ^ n) = 0 := by
        rw [← Valuation.embedding_restrict, h0, map_zero]
      exact pow_ne_zero n hϖ0 ((Valuation.zero_iff _).1 h1)
    · intro s hs
      obtain ⟨u, hu, hus⟩ := mem_nhds_subtype _ _ _ |>.1 hs
      rw [ZeroMemClass.coe_zero, Valued.mem_nhds_zero] at hu
      obtain ⟨γ, hγ⟩ := hu
      obtain ⟨n, hn⟩ := Valued.exists_pow_lt_of_le_exp_neg_one (R := w.adicCompletion E) hϖ.le
        (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
          (f := (.ofClass (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))))) γ)
      refine ⟨n, fun a ha => hus (hγ ?_)⟩
      show (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).restrict
        (a : w.adicCompletion E) < γ.1
      rw [Valuation.restrict_lt_iff_lt_embedding]
      exact lt_of_le_of_lt ((hpow n a).1 ha) (by simpa using hn)
  have hcl : IsClosed ((w.adicCompletionIntegers E : Set (w.adicCompletion E))) :=
    Valued.isClosed_valuationSubring _
  have : CompleteSpace (w.adicCompletionIntegers E) := hcl.completeSpace_coe
  exact hadic.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

private lemma neg_log_valuation_eq_ordL (x : w.adicCompletion E) : -WithZero.log (Valued.v x) = ordL x := by
  unfold ordL
  split_ifs with h
  · rw [h, WithZero.log_zero, neg_zero]
  · congr 1
    conv_lhs => rw [← WithZero.coe_unzero h]
    rfl

theorem exists_uq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∃ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) ∧ (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) ∧ (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) ∧ qV E w = K.q ^ 2 := by
  intro E _ _ _ hU w hw
  obtain ⟨-, hcc, hiso, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨-, ⟨ϖ, q, hUI, hq⟩, -, -⟩ := hns hw
  obtain ⟨-, -, -, hϖ, ⟨x₀, hx₀, hx₀'⟩, hq2, hcard⟩ := hUI
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hc : Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) = q ^ 2 := hcard
  have := isAdicComplete_maximalIdeal_adicCompletionIntegers w ϖ hϖ'
  have : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hc]
    exact pow_ne_zero 2 (by omega)
  have : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  let σ : w.adicCompletion E ≃+* w.adicCompletion E :=
    RingEquiv.ofRingHom (cj w) (cj w) (RingHom.ext hcc) (RingHom.ext hcc)
  have hx₀A : Valued.v x₀ ≤ 1 := hx₀
  have hσx₀ : Valued.v (σ x₀) ≤ 1 := by
    show Valued.v (cj w x₀) ≤ 1
    rw [hiso]
    exact hx₀A
  have hint : ∀ x : w.adicCompletionIntegers E, ∃ y : w.adicCompletionIntegers E,
      σ (algebraMap _ (w.adicCompletion E) x) = algebraMap _ (w.adicCompletion E) y := by
    intro x
    have hx : Valued.v (σ x) ≤ 1 := by
      show Valued.v (cj w x) ≤ 1
      rw [hiso]
      exact x.2
    exact ⟨⟨σ x, hx⟩, rfl⟩
  have hres : ∃ x y : w.adicCompletionIntegers E,
      σ (algebraMap _ (w.adicCompletion E) x) = algebraMap _ (w.adicCompletion E) y ∧
        x - y ∉ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) := by
    refine ⟨⟨x₀, hx₀A⟩, ⟨σ x₀, hσx₀⟩, rfl, fun hm => ?_⟩
    have h1 := (mem_max_iff w _).1 hm
    have h2 : Valued.v (x₀ - σ x₀) = 1 := by
      rw [Valuation.map_sub_swap]
      exact hx₀'
    push_cast at h1
    rw [h2] at h1
    exact lt_irrefl _ h1
  let K : GlobalTheory.UnitLemma.UQ :=
    { O := w.adicCompletionIntegers E
      E := w.adicCompletion E
      c := σ
      c_c := hcc
      c_int := hint
      c_res := hres
      q := q
      card_res := hc }
  refine ⟨K, RingEquiv.refl _, fun x => rfl, ?_, ?_, hq⟩
  · intro x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro h
      exact ⟨⟨x, h⟩, rfl⟩
  · intro x
    show -WithZero.log ((IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) x) = ordL x
    rw [valuation_max_eq w ϖ hϖ' x]
    exact neg_log_valuation_eq_ordL w x

end GlobalTheory.InertUQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedStableSubgroupSemiAbelianNoTorsion
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OStableClosed
open GlobalTheory.RationalPoint

theorem finite_of_isClosed_of_no_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (π : 𝓞 E), IsSemiAbelian G → π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  intro E _ _ k _ _ _ G _ act π hG hπ hπu C Z hZ hC hstab htor
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  obtain ⟨T⟩ := GlobalTheory.TorsionDense.nonempty_torusExtension G hG
  letI := T.addCommGroup
  letI := T.free
  letI := T.finite
  letI := T.grpB
  haveI := T.q_hom
  haveI := T.i_hom
  haveI := T.isAbelian.proper
  haveI := T.isAbelian.smooth
  haveI := act.hom π
  obtain ⟨actB, actT, hB, hT⟩ := GlobalTheory.T.exists_ringAction_torus_and_abelian_quotient (𝓞 E) k G act hG T
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ T.B) :=
    MonoidHom.mk' (fun x => x ≫ T.q) fun x y => MonObj.mul_comp x y T.q
  let j : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) T.X) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ T.i) fun x y => MonObj.mul_comp x y T.i
  let m : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ act.act π) fun x y => MonObj.mul_comp x y _
  have hj : Function.Injective j := fun x y hxy =>
    T.isKernel.hom_ext hxy (toUnit_unique _ _)
  have hker : ∀ x, φ x = 1 → ∃ t, j t = x := fun x hx =>
    ⟨T.isKernel.lift x (toUnit _) hx, T.isKernel.lift_fst _ _ _⟩
  have hTf : Finite (C.comap j) := by
    refine GlobalTheory.T.finite_closed_torus_subgroup_without_pi_torsion E k T.X actT π hπ hπu _ (T.i.left ⁻¹' Z)
      (hZ.preimage T.i.left.continuous) (fun x => ?_) (fun a x hx => ?_) (fun x hx h1 => ?_)
    · rw [Subgroup.mem_comap, hC, range_left_subset_iff, range_left_subset_iff]
      rfl
    · rw [Subgroup.mem_comap] at hx ⊢
      change (x ≫ actT.act a) ≫ T.i ∈ C
      rw [Category.assoc, hT a, ← Category.assoc]
      exact hstab a _ hx
    · apply hj
      rw [map_one]
      refine htor _ hx ?_
      change (x ≫ T.i) ≫ act.act π = 1
      rw [Category.assoc, ← hT π, ← Category.assoc, h1, MonObj.one_comp]
  let ψ : C →* (𝟙_ (Over (Sp k)) ⟶ T.B) := φ.comp C.subtype
  have hK : Finite ψ.ker := by
    choose s hs using fun x : ψ.ker => hker x.1.1 x.2
    refine Finite.of_injective
      (fun x : ψ.ker => (⟨s x, by rw [Subgroup.mem_comap, hs]; exact x.1.2⟩ : C.comap j))
      fun x y hxy => ?_
    have := congrArg (fun t : C.comap j => j t.1) hxy
    simp only [hs] at this
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G T.B T.q inferInstance
    inferInstance inferInstance inferInstance inferInstance C Z hZ hC
  have hR : Finite ψ.range := by
    refine GlobalTheory.T.finite_closed_ringStable_subgroup_abelian_no_torsion E k T.B actB π T.isAbelian hπ hπu _ Z' hZ' (fun y => ?_) (fun a y hy => ?_) ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩⟩
    · obtain ⟨x, rfl⟩ := hy
      refine ⟨⟨x.1 ≫ act.act a, hstab a _ x.2⟩, ?_⟩
      change (x.1 ≫ act.act a) ≫ T.q = (x.1 ≫ T.q) ≫ actB.act a
      rw [Category.assoc, Category.assoc, hB]
    · rintro _ ⟨y, rfl⟩ hy
      have hmC : ∀ z : C, m z.1 ∈ C := fun z => hstab π _ z.2
      have hmK : ∀ z : ψ.ker, ψ ⟨m z.1.1, hmC z.1⟩ = 1 := fun z => by
        change (z.1.1 ≫ act.act π) ≫ T.q = 1
        rw [Category.assoc, ← hB π, ← Category.assoc]
        change ψ z.1 ≫ actB.act π = 1
        rw [MonoidHom.mem_ker.1 z.2]
        haveI := actB.hom π
        exact MonObj.one_comp _
      let f : ψ.ker → ψ.ker := fun z => ⟨⟨m z.1.1, hmC z.1⟩, hmK z⟩
      have hf : Function.Injective f := fun z₁ z₂ h => by
        have h1 : m z₁.1.1 = m z₂.1.1 := congrArg (fun z : ψ.ker => z.1.1) h
        have h2 : z₁.1.1 / z₂.1.1 = 1 := htor _ (C.div_mem z₁.1.2 z₂.1.2) (by
          change m (z₁.1.1 / z₂.1.1) = 1
          rw [map_div, h1, div_self'])
        exact Subtype.ext (Subtype.ext (div_eq_one.1 h2))
      have hw : ψ ⟨m y.1, hmC y⟩ = 1 := by
        change (y.1 ≫ act.act π) ≫ T.q = 1
        rw [Category.assoc, ← hB π, ← Category.assoc]
        exact hy
      obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.1 hf) ⟨⟨m y.1, hmC y⟩, hw⟩
      have h1 : m z.1.1 = m y.1 := congrArg (fun z : ψ.ker => z.1.1) hz
      have h2 : y.1 / z.1.1 = 1 := htor _ (C.div_mem y.2 z.1.2) (by
        change m (y.1 / z.1.1) = 1
        rw [map_div, h1, div_self'])
      have h3 : y = z.1 := Subtype.ext (div_eq_one.1 h2)
      rw [h3]
      exact z.2
  exact (MonoidHom.finite_iff_finite_ker_range ψ).2 ⟨hK, hR⟩

end GlobalTheory.OStableClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHeightSubMeanLeDegreeFullLatticeDetIdeal
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSShort.DetIdeal

theorem detSpan_relIndex_le : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (β : Module.Basis (Fin d) F V) (N₀ N : Submodule (𝓞 F) V), N₀ ≤ N → N₀.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 → Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ N₀) ∧ y = β.det w} ≠ ⊥ → (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ N) ∧ y = β.det w}, c • y ∈ (1 : Submodule (𝓞 F) F)) → (Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ N₀) ∧ y = β.det w}).toAddSubgroup.relIndex (Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ N) ∧ y = β.det w}).toAddSubgroup ≤ N₀.toAddSubgroup.relIndex N.toAddSubgroup := by
  intro F V _ _ _ _ _ _ d β N₀ N hle hidx hne hbdd
  classical
  set A : Submodule (𝓞 F) V → Submodule (𝓞 F) F :=
    fun P => Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ P) ∧ y = β.det w} with hA
  have hmono : ∀ P P' : Submodule (𝓞 F) V, P ≤ P' → A P ≤ A P' := fun P P' h =>
    Submodule.span_mono fun y ⟨w, hw, hy⟩ => ⟨w, fun i => h (hw i), hy⟩
  show (A N₀).toAddSubgroup.relIndex (A N).toAddSubgroup ≤ N₀.toAddSubgroup.relIndex N.toAddSubgroup
  obtain ⟨c, hc0, hc⟩ := hbdd
  induction hn : N₀.toAddSubgroup.relIndex N.toAddSubgroup using Nat.strong_induction_on generalizing N₀ with
  | _ n ih =>
  rcases eq_or_lt_of_le hle with rfl | hlt
  · rw [AddSubgroup.relIndex_self]
    omega
  obtain ⟨u, p, hp, huN, hu0, hpu⟩ := GlobalTheory.T.exists_maximalIdeal_smul_mem_of_lt_of_relIndex_ne_zero F V N₀ N hlt hidx
  set N₁ := N₀ ⊔ Submodule.span (𝓞 F) {u} with hN₁
  have h01 : N₀ ≤ N₁ := le_sup_left
  have h1N : N₁ ≤ N := sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).mpr huN)
  have hidx01 := GlobalTheory.T.relIndex_sup_span_singleton_eq_absNorm_of_isMaximal F V N₀ u p hp hu0 hpu
  have hmul := AddSubgroup.relIndex_mul_relIndex N₀.toAddSubgroup N₁.toAddSubgroup N.toAddSubgroup
    (Submodule.toAddSubgroup_mono h01) (Submodule.toAddSubgroup_mono h1N)
  rw [hidx01] at hmul
  have hpN : Ideal.absNorm p ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hmul; exact hidx hmul.symm
  have hp1 : 1 < Ideal.absNorm p := by
    rcases Nat.lt_or_ge 1 (Ideal.absNorm p) with h | h
    · exact h
    · exfalso
      have : Ideal.absNorm p = 1 := by omega
      exact hp.ne_top (Ideal.absNorm_eq_one_iff.mp this)
  have hidx1 : N₁.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact hidx hmul.symm
  have hlt' : N₁.toAddSubgroup.relIndex N.toAddSubgroup < n := by
    rw [← hn, ← hmul]
    exact lt_mul_left (Nat.pos_of_ne_zero hidx1) hp1
  have hne1 : A N₁ ≠ ⊥ := fun h => hne (le_bot_iff.mp (h ▸ hmono _ _ h01))
  have ih' := ih _ hlt' N₁ h1N hidx1 hne1 rfl

  have hpA : p • A N₁ ≤ A N₀ := by
    rw [Submodule.smul_le]
    intro π hπ y hy
    exact GlobalTheory.T.smul_detSpan_sup_le_detSpan_lattice F V d β N₀ u π (hpu π hπ) y hy
  have hp0 : p ≠ ⊥ := by
    rintro rfl; exact hpN (by simp)
  have hfr := GlobalTheory.T.relIndex_ideal_smul_fractionalIdeal_eq_absNorm_numberField F (A N₁) p hp0 hne1 ⟨c, hc0, fun y hy => hc y (hmono _ _ h1N hy)⟩
  have hstep : (A N₀).toAddSubgroup.relIndex (A N₁).toAddSubgroup ≤ Ideal.absNorm p := by
    rw [← hfr]
    exact AddSubgroup.relIndex_le_of_le_left (Submodule.toAddSubgroup_mono hpA) (by rw [hfr]; exact hpN)
  have hmulA := AddSubgroup.relIndex_mul_relIndex (A N₀).toAddSubgroup (A N₁).toAddSubgroup (A N).toAddSubgroup
    (Submodule.toAddSubgroup_mono (hmono _ _ h01)) (Submodule.toAddSubgroup_mono (hmono _ _ h1N))
  rw [← hmulA, ← hn, ← hmul]
  exact Nat.mul_le_mul hstep ih'

theorem finPart_sub_mean_le_deg : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (nm : HermFam F V) (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V), IsFull M → ∀ (τ : Type) (g : MvPolynomial τ F), g ≠ 0 → (∀ m, coeff m g ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v}) → finPart g - mean F (fun σ => Real.log (nm.gram σ b).det.re) / 2 ≤ deg nm M := by
  intro F V _ _ _ _ _ _ nm M d b hM τ g hg hcoef
  classical
  have hfg := hM.fg
  have hsp := hM.span
  obtain ⟨r, v, hv⟩ : ∃ (r : ℕ) (v : Fin r → V), IsFrame F M v := ⟨_, exists_isFrame M hfg⟩
  have hspan : ⊤ ≤ Submodule.span F (Set.range v) := by
    rw [← hsp]
    exact Submodule.span_le.mpr hv.2.2
  let β : Module.Basis (Fin r) F V := Module.Basis.mk hv.2.1 hspan
  have hβ : ⇑β = v := Module.Basis.coe_mk _ _
  obtain rfl : r = d := by simpa using Fintype.card_congr (β.indexEquiv b)
  set δ := b.det v with hδ
  have hδ0 : δ ≠ 0 := by
    have := (b.isUnit_det β).ne_zero
    rwa [hβ] at this
  set L := Submodule.span (𝓞 F) (Set.range v) with hL
  set B := Submodule.span (𝓞 F) {y | ∃ w : Fin r → V, (∀ i, w i ∈ M) ∧ y = β.det w} with hB

  have hdet : ∀ w : Fin r → V, b.det w = δ * β.det w := fun w => by
    rw [hδ, ← hβ, Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul,
      Module.Basis.toMatrix_mul_toMatrix]
  have hcoef' : ∀ m, coeff m g / δ ∈ B := fun m => by
    let φ : F →ₗ[𝓞 F] F := (LinearMap.mulLeft F δ⁻¹).restrictScalars (𝓞 F)
    have hmap : (Submodule.span (𝓞 F) {y | ∃ v : Fin r → V, (∀ i, v i ∈ M) ∧ y = b.det v}).map φ ≤ B := by
      rw [Submodule.map_span_le]
      rintro _ ⟨w, hw, rfl⟩
      have : φ (b.det w) = β.det w := by
        simp only [φ, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply, hdet]
        field_simp
      rw [this]
      exact Submodule.subset_span ⟨w, hw, rfl⟩
    have := hmap (Submodule.mem_map_of_mem (f := φ) (hcoef m))
    simpa [φ, div_eq_inv_mul] using this
  have hLM : L ≤ M := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv.1 i)
  have hidx : L.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := hv.relIndex_ne_zero hfg
  have hbase := GlobalTheory.T.span_basis_det_integral_eq_one F V r β
  rw [hβ] at hbase
  have hbdd := GlobalTheory.T.exists_common_denominator_span_det F V r β M hfg
  have hind := detSpan_relIndex_le F V r β L M hLM hidx (by rw [hbase]; intro h; have h1 : (1 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.one_le.mp le_rfl; rw [h] at h1; simp at h1) hbdd
  rw [hbase] at hind
  have h1B : (1 : Submodule (𝓞 F) F) ≤ B := by
    rw [← hbase]
    exact Submodule.span_mono fun y ⟨w, hw, hy⟩ => ⟨w, fun i => hLM (hw i), hy⟩
  have hgauss := GlobalTheory.T.finsum_log_gaussAbs_le_fractionalIdeal_index F τ g hg B δ hδ0 h1B hbdd hcoef'
  have hprod := GlobalTheory.T.finsum_log_finitePlace_eq_neg_log_abs_norm' F δ hδ0
  have hn : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos

  have hG : ∀ σ : F →+* ℂ, Real.log (nm.gram σ v).det.re = Real.log (Complex.normSq (σ δ)) + Real.log (nm.gram σ b).det.re := by
    intro σ
    rw [GlobalTheory.T.hermFam_gram_det_eq_normSq_basis_det_mul F V nm σ r b v, ← hδ]
    have hpos : 0 < (nm.gram σ ⇑b).det.re := by
      have := (nm.posDef σ r b b.linearIndependent).det_pos
      exact (Complex.pos_iff.mp this).1
    have hn0 : 0 < Complex.normSq (σ δ) := Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hδ0)
    rw [Complex.re_ofReal_mul, Real.log_mul hn0.ne' hpos.ne']
  have hsum := ds_sum_log_normSq_embeddings δ hδ0
  rw [arakelovDegree_eq_degreeOfFamily nm hfg hv, degreeOfFamily, finPart, mean]
  simp only [hG, Finset.sum_add_distrib, hsum]
  have hlog : Real.log ((1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex B.toAddSubgroup : ℝ) ≤ Real.log (L.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
    rcases Nat.eq_zero_or_pos ((1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex B.toAddSubgroup) with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hidx)
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hind)
  have hkey : ∑ᶠ q : FinitePlace F, Real.log (gaussAbs q g) ≤
      Real.log (L.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) - Real.log |((Algebra.norm ℚ δ : ℚ) : ℝ)| := by
    linarith
  calc _ = ((∑ᶠ q : FinitePlace F, Real.log (gaussAbs q g)) - (∑ σ : F →+* ℂ, Real.log (nm.gram σ ⇑b).det.re) / 2) /
        (Module.finrank ℚ F : ℝ) := by ring
    _ ≤ (Real.log (L.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) - 1 / 2 * (2 * Real.log |((Algebra.norm ℚ δ : ℚ) : ℝ)| +
        ∑ σ : F →+* ℂ, Real.log (nm.gram σ ⇑b).det.re)) / (Module.finrank ℚ F : ℝ) := by
      apply div_le_div_of_nonneg_right _ hn.le
      linarith
    _ = _ := by ring

end GlobalTheory.HSShort.DetIdeal
end
end

