import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBorelInvariantTestFunctionFrameChart
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar.TestFn

theorem exists_invariant_test : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r), ∃ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧ ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ 0 ∧ ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ ⊤ := by
  intro E _ _ _ r X
  have ho : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
  have h0 := IW.zero_mem_OmF X (baseFr X) ho
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((OntoB.isOpen_OmF X (baseFr X)).mem_nhds h0)
  set A : Set (V (nd X)) := Metric.closedBall 0 ε with hAdef
  have hA : MeasurableSet A := measurableSet_closedBall
  have hS := GlobalTheory.Unfold.measurableSet_satFrames X ho hA hball
  refine ⟨(GlobalTheory.Unfold.satFrames X (baseFr X) A).indicator 1, measurable_one.indicator hS, ?_, ?_⟩
  · intro x _ b hb
    by_cases hx : x ∈ GlobalTheory.Unfold.satFrames X (baseFr X) A
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem ((GlobalTheory.Unfold.rmul_mem_satFrames_iff X _ A x hb).mpr hx)]
      rfl
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem fun h => hx ((GlobalTheory.Unfold.rmul_mem_satFrames_iff X _ A x hb).mp h)]
  have heq : (fun z => (GlobalTheory.Unfold.satFrames X (baseFr X) A).indicator (1 : Frame X.Ψ r → ℝ≥0∞)
      (cpt X (baseFr X) z)) = A.indicator 1 := by
    funext z
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz,
        Set.indicator_of_mem ((GlobalTheory.Unfold.cpt_mem_satFrames_iff X ho A z).mpr hz)]
      rfl
    · rw [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem fun h => hz ((GlobalTheory.Unfold.cpt_mem_satFrames_iff X ho A z).mp h)]
  rw [heq, lintegral_indicator_one hA]
  refine ⟨?_, (GlobalTheory.SatFin.muF_lt_top_of_isCompact X (baseFr X) (isCompact_closedBall _ _) hball).ne⟩
  unfold muF
  have hmeas : AEMeasurable (fun z => ENNReal.ofReal (densF X (baseFr X) z))
      (volume.restrict (OmF X (baseFr X))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (OntoB.densF_continuousOn.aemeasurable (OntoB.isOpen_OmF X (baseFr X)).measurableSet)
  rw [Ne, withDensity_apply_eq_zero' hmeas]
  have hset : {z | ENNReal.ofReal (densF X (baseFr X) z) ≠ 0} ∩ A = A := by
    refine Set.inter_eq_right.mpr fun z hz => ?_
    show ENNReal.ofReal (densF X (baseFr X) z) ≠ 0
    exact (ENNReal.ofReal_pos.mpr (OntoB.densF_pos (hball hz))).ne'
  rw [hset, Measure.restrict_apply hA, Set.inter_eq_left.mpr hball]
  exact (Metric.measure_closedBall_pos volume 0 hε).ne'

end GlobalTheory.FlagQuotHaar.TestFn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeFiniteIntersection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem closedSubscheme_iInter_exists :
    ∀ (H : Scheme.{0}) (Idx : Type) [Finite Idx] (Z : Idx → Scheme.{0}) (i : ∀ k, Z k ⟶ H),
      (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧
        ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h := by
  intro H Idx _ Z i hi
  revert Z i hi
  refine Finite.induction_empty_option
    (P := fun (α : Type) => ∀ (Z : α → Scheme.{0}) (i : ∀ k, Z k ⟶ H),
      (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧
        ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h)
    ?_ ?_ ?_ Idx
  · intro α β e ih Z i hi
    obtain ⟨Z₀, i₀, h₀, hp⟩ := ih (fun a => Z (e a)) (fun a => i (e a)) (fun a => hi (e a))
    refine ⟨Z₀, i₀, h₀, fun T h => (hp T h).trans ?_⟩
    exact e.forall_congr_right (q := fun k => ∃ z, z ≫ i k = h)
  · intro Z i _
    refine ⟨H, 𝟙 H, inferInstance, fun T h => ⟨fun _ k => k.elim, fun _ => ⟨h, Category.comp_id h⟩⟩⟩
  · intro α _ ih Z i hi
    obtain ⟨Z₀, i₀, h₀, hp⟩ := ih (fun a => Z (some a)) (fun a => i (some a)) (fun a => hi (some a))
    haveI := h₀
    haveI := hi none
    refine ⟨Limits.pullback i₀ (i none), Limits.pullback.fst i₀ (i none) ≫ i₀, inferInstance, ?_⟩
    intro T h
    rw [Option.forall, ← hp T h]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨⟨z ≫ Limits.pullback.snd _ _, ?_⟩, ⟨z ≫ Limits.pullback.fst _ _, ?_⟩⟩
      · rw [Category.assoc, ← Limits.pullback.condition]
      · rfl
    · rintro ⟨⟨z₂, h₂⟩, ⟨z₁, h₁⟩⟩
      exact ⟨Limits.pullback.lift z₁ z₂ (h₁.trans h₂.symm), by rw [Limits.pullback.lift_fst_assoc, h₁]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeIntersection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem closedSubscheme_inter_exists : ∀ (H Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ H) (i₂ : Z₂ ⟶ H),
    IsClosedImmersion i₁ → IsClosedImmersion i₂ → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H),
      IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H),
        (∃ z, z ≫ i₀ = h) ↔ (∃ z, z ≫ i₁ = h) ∧ ∃ z, z ≫ i₂ = h := by
  intro H Z₁ Z₂ i₁ i₂ h₁ h₂
  refine ⟨pullback i₁ i₂, pullback.snd i₁ i₂ ≫ i₂, inferInstance, ?_⟩
  intro T h
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z ≫ pullback.fst i₁ i₂, ?_⟩, ⟨z ≫ pullback.snd i₁ i₂, ?_⟩⟩
    · rw [Category.assoc, pullback.condition]
    · rw [Category.assoc]
  · rintro ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩
    exact ⟨pullback.lift z₁ z₂ (hz₁.trans hz₂.symm), by rw [← Category.assoc, pullback.lift_snd, hz₂]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCohomologyDerivativeRelationOfFrame
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem dRel_of_frame_exists (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) :
    HasFrame F → ∀ x : GlobalTheory.CatCoh.H1 F, ∃ (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w := by
  rintro ⟨n, ⟨fr⟩⟩ x
  obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F x
  let g : Fin n → Z1 F := fun i ↦ ⟨fun T T' φ ↦ fr.δ i T' (D R (F.obj T') (f.1 T T' φ)), by
    intro T T' T'' φ ψ
    simp only
    rw [Z1.comp f φ ψ, map_add, map_add, ← p1_D, fr.nat]⟩
  refine ⟨n, fun i ↦ GlobalTheory.CatCoh.H1.mk F (g i), fr.w, f, g, 0, rfl, fun _ ↦ rfl, ?_⟩
  intro T T' φ
  simp only [Pi.zero_apply, map_zero, sub_zero, add_zero]
  exact fr.sum T' _

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSimilitudeLevelTower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.TowerLev

theorem compat_seq {X : Type} (A : ℕ → Set X) (hfin : ∀ j, (A j).Finite)
    (hne : ∀ j, (A j).Nonempty) (φ : ℕ → X → X) (hφ : ∀ j, ∀ x ∈ A (j + 1), φ j x ∈ A j) :
    ∃ s : ℕ → X, ∀ j, s j ∈ A j ∧ φ j (s (j + 1)) = s j := by
  let F : ℕᵒᵖ ⥤ Type := Functor.ofOpSequence (X := fun j => ↥(A j))
    (fun j => TypeCat.ofHom (fun x => ⟨φ j x.1, hφ j x.1 x.2⟩ : ↥(A (j + 1)) → ↥(A j)))
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun j => (s (Opposite.op j)).1, fun j => ⟨(s (Opposite.op j)).2, ?_⟩⟩
  have h := hs (homOfLE (Nat.le_add_right j 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact congrArg Subtype.val h

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] {Q : Type} [CommGroup Q]

def IsLev (D : Datum p) (act : D.O → Q → Q) (W : ℕ → Q → Q → kˣ) (ζ : ℕ → kˣ) (r : ℕ) (f : D.La → Q) : Prop :=
  ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧
    (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) ∧
    ∀ x y, W r (f x) (f y) = ζ r ^ D.EF x y

variable {D : Datum p}

theorem map_zero_of_add {f : D.La → Q} (hf : ∀ x y, f (x + y) = f x * f y) : f 0 = 1 := by
  have h := hf 0 0
  rw [add_zero] at h
  simpa using h.symm

theorem map_nsmul_of_add {f : D.La → Q} (hf : ∀ x y, f (x + y) = f x * f y) (n : ℕ) (x : D.La) :
    f (n • x) = f x ^ n := by
  induction n with
  | zero => simp [map_zero_of_add hf]
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem cancel_nsmul (D : Datum p) (n : ℕ) (hn : n ≠ 0) {a b : D.La} (h : n • a = n • b) : a = b := by
  haveI := D.freeLa
  have h' : (n : ℤ) • a = (n : ℤ) • b := by simpa [natCast_zsmul] using h
  exact smul_right_injective D.La (by exact_mod_cast hn : (n : ℤ) ≠ 0) h'

theorem IsLev.step {act : D.O → Q → Q} {W : ℕ → Q → Q → kˣ} {ζ : ℕ → kˣ}
    (hact : ∀ c a b, act c (a * b) = act c a * act c b) (hζ : ∀ r, ζ (r + 1) ^ p = ζ r)
    (hW : ∀ r (a b : Q), a ^ (p ^ (r + 1)) = 1 → b ^ (p ^ (r + 1)) = 1 →
      W r (a ^ p) (b ^ p) = W (r + 1) a b ^ p)
    (r : ℕ) (f : D.La → Q) (hf : IsLev D act W ζ (r + 1) f) : IsLev D act W ζ r (fun x => f x ^ p) := by
  obtain ⟨⟨hadd, hlin, hker, honto⟩, hpair⟩ := hf
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hkill : ∀ x, f x ^ (p ^ (r + 1)) = 1 := fun x => (honto _).2 ⟨x, rfl⟩
  refine ⟨⟨fun x y => ?_, fun c x => ?_, fun x => ?_, fun g => ?_⟩, fun x y => ?_⟩
  · simp only
    rw [hadd, mul_pow]
  · simp only
    rw [hlin]
    exact (map_pow (MonoidHom.mk' (act c) (hact c)) (f x) p).symm
  · simp only
    rw [← map_nsmul_of_add hadd, hker]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, cancel_nsmul D p hp0 (by rw [hy, pow_succ', mul_smul])⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [pow_succ', mul_smul]⟩
  · simp only
    constructor
    · intro hg
      have hg' : g ^ (p ^ (r + 1)) = 1 := by rw [pow_succ, pow_mul, hg, one_pow]
      obtain ⟨x, rfl⟩ := (honto g).1 hg'
      rw [← map_nsmul_of_add hadd, hker] at hg
      obtain ⟨y, hy⟩ := hg
      have hx : x = p • y := cancel_nsmul D (p ^ r) (pow_ne_zero _ hp0) (by rw [hy, pow_succ, mul_smul])
      exact ⟨y, by rw [hx, map_nsmul_of_add hadd]⟩
    · rintro ⟨x, rfl⟩
      rw [← pow_mul, ← pow_succ', hkill]
  · simp only
    rw [hW r (f x) (f y) (hkill x) (hkill y), hpair, ← hζ r, ← zpow_natCast (ζ (r + 1) ^ _),
      ← zpow_natCast (ζ (r + 1)), ← zpow_mul, ← zpow_mul, mul_comm]

theorem finite_range_of_add {f : D.La → Q} (hadd : ∀ x y, f (x + y) = f x * f y) {n : ℕ} (hn : n ≠ 0)
    (hker : ∀ y, f (n • y) = 1) : (Set.range f).Finite := by
  haveI := D.freeLa
  haveI := D.finLa
  let B := Module.Free.chooseBasis ℤ D.La
  have hpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine ((Set.Finite.pi (fun _ : Module.Free.ChooseBasisIndex ℤ D.La => Set.finite_Ico (0 : ℤ) n)).image
    (fun v => f (∑ i, v i • B i))).subset ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨fun i => B.repr x i % n, fun i _ => ⟨Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩, ?_⟩
  have hx : x = ∑ i, (B.repr x i % n) • B i + n • ∑ i, (B.repr x i / n) • B i := by
    rw [← natCast_zsmul, Finset.smul_sum, ← Finset.sum_add_distrib]
    conv_lhs => rw [← B.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← add_smul, Int.emod_add_mul_ediv]
  rw [congrArg f hx, hadd, hker, _root_.mul_one]

def toLin (f : D.La → Q) (hf : ∀ x y, f (x + y) = f x * f y) : D.La →ₗ[ℤ] Additive Q :=
  (AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) (fun x y => by rw [hf]; rfl)).toIntLinearMap

theorem finite_isLev {act : D.O → Q → Q} {W : ℕ → Q → Q → kˣ} {ζ : ℕ → kˣ} (r : ℕ) :
    {f | IsLev D act W ζ r f}.Finite := by
  rcases Set.eq_empty_or_nonempty {f | IsLev D act W ζ r f} with h | ⟨f0, hf0⟩
  · rw [h]; exact Set.finite_empty
  haveI := D.freeLa
  haveI := D.finLa
  let B := Module.Free.chooseBasis ℤ D.La
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hT : (Set.range f0).Finite :=
    finite_range_of_add hf0.1.1 (pow_ne_zero r hp0) (fun y => (hf0.1.2.2.1 _).2 ⟨y, rfl⟩)
  refine Set.Finite.of_finite_image (f := fun f : D.La → Q => fun i => f (B i)) ?_ ?_
  · refine (Set.Finite.pi (fun _ => hT)).subset ?_
    rintro _ ⟨f, hf, rfl⟩ i _
    exact (hf0.1.2.2.2 _).1 ((hf.1.2.2.2 _).2 ⟨B i, rfl⟩)
  · intro f hf g hg hfg
    have key : toLin f hf.1.1 = toLin g hg.1.1 :=
      B.ext (fun i => congrArg Additive.ofMul (congrFun hfg i))
    funext x
    exact congrArg Additive.toMul (LinearMap.congr_fun key x)

theorem exists_compatible : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q]
    (act : D.O → Q → Q) (W : ℕ → Q → Q → kˣ) (ζ : ℕ → kˣ), (∀ c a b, act c (a * b) = act c a * act c b) →
    (∀ r, ζ (r + 1) ^ p = ζ r) →
    (∀ r (a b : Q), a ^ (p ^ (r + 1)) = 1 → b ^ (p ^ (r + 1)) = 1 → W r (a ^ p) (b ^ p) = W (r + 1) a b ^ p) →
    (∀ r, ∃ f : D.La → Q, ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧
      (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) ∧
      ∀ x y, W r (f x) (f y) = ζ r ^ D.EF x y) →
    ∃ ev : ℕ → D.La → Q, (∀ r, ((∀ x y, ev r (x + y) = ev r x * ev r y) ∧
      (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧
      (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) ∧ ∀ x y, W r (ev r x) (ev r y) = ζ r ^ D.EF x y) ∧
      ∀ r x, ev (r + 1) x ^ p = ev r x := by
  intro p _ D k _ Q _ act W ζ hact hζ hW hex
  obtain ⟨s, hs⟩ := compat_seq (fun r => {f | IsLev D act W ζ r f}) (fun r => finite_isLev r) hex
    (fun _ f x => f x ^ p) (fun r f hf => IsLev.step hact hζ hW r f hf)
  exact ⟨s, fun r => (hs r).1, fun r x => congrFun (hs r).2 x⟩

end GlobalTheory.TowerLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexLinearOfPureTypesFiniteIndexStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexLinear_of_pure_types_finite_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P') (Φ : D.La ≃ₗ[𝓞 E] D'.La) (N : ℕ), 0 < N → (∀ v : D.La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) → (∀ a ∈ lat hP H.rt0, Φ a ∈ lat hP' H.rt0) → (∀ a ∈ lat hP (-H.rt0), Φ a ∈ lat hP' (-H.rt0)) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' (Φ a) = L (P a) := by
  first | exact @GlobalTheory.CompRat.exists_complex_linear_of_pure_types_of_index | exact GlobalTheory.CompRat.exists_complex_linear_of_pure_types_of_index | (intros; apply GlobalTheory.CompRat.exists_complex_linear_of_pure_types_of_index <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjIdempotentModPrimePow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.SplitIdem

theorem isCoprime_deriv {p : ℕ} (hp : p.Prime) {t n ρ : ℤ} (hd : ¬ (p : ℤ) ∣ t ^ 2 - 4 * n)
    (h : (p : ℤ) ∣ ρ ^ 2 - t * ρ + n) : IsCoprime (2 * ρ - t) (p : ℤ) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  refine ((hp'.irreducible.coprime_iff_not_dvd).mpr ?_).symm
  intro h2
  apply hd
  have : t ^ 2 - 4 * n = (2 * ρ - t) * (2 * ρ - t) - 4 * (ρ ^ 2 - t * ρ + n) := by ring
  rw [this]
  exact dvd_sub (h2.mul_right _) (h.mul_left _)

theorem exists_root_pow {p : ℕ} (hp : p.Prime) {t n : ℤ} (hd : ¬ (p : ℤ) ∣ t ^ 2 - 4 * n)
    (h : ∃ ρ : ℤ, (p : ℤ) ∣ ρ ^ 2 - t * ρ + n) (k : ℕ) :
    ∃ ρ : ℤ, (p : ℤ) ^ (k + 1) ∣ ρ ^ 2 - t * ρ + n := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    obtain ⟨ρ, c, hc⟩ := ih
    have h1 : (p : ℤ) ∣ ρ ^ 2 - t * ρ + n := by
      rw [hc]; exact (dvd_pow_self _ (Nat.succ_ne_zero k)).mul_right _
    obtain ⟨a, b, hab⟩ := isCoprime_deriv hp hd h1
    refine ⟨ρ - (p : ℤ) ^ (k + 1) * c * a, c * b + (p : ℤ) ^ k * c ^ 2 * a ^ 2, ?_⟩
    linear_combination hc - (p : ℤ) ^ (k + 1) * c * hab

theorem exists_conj_idem : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℕ), ∃ ε u v : 𝓞 D.F,
    ε + D.bar ε = 1 + (p : 𝓞 D.F) ^ r * u ∧ ε * D.bar ε = (p : 𝓞 D.F) ^ r * v := by
  intro p hp D r
  obtain ⟨ρ, c, hc⟩ := exists_root_pow hp.out D.disc_p D.split r
  have h1 : (p : ℤ) ∣ ρ ^ 2 - D.tr * ρ + D.nm := by
    rw [hc]; exact (dvd_pow_self _ (Nat.succ_ne_zero r)).mul_right _
  obtain ⟨s, b, hsb⟩ := (isCoprime_deriv hp.out D.disc_p h1).pow_right (n := r)
  have hc' := congrArg (Int.cast : ℤ → 𝓞 D.F) hc
  have hsb' := congrArg (Int.cast : ℤ → 𝓞 D.F) hsb
  push_cast at hc' hsb'
  have ht := D.tr_eq
  have hn := D.nm_eq
  refine ⟨(s : 𝓞 D.F) * ((ρ : 𝓞 D.F) - D.ω), -(b : 𝓞 D.F), (s : 𝓞 D.F) ^ 2 * (p : 𝓞 D.F) * (c : 𝓞 D.F), ?_, ?_⟩
  · rw [map_mul, map_sub, map_intCast, map_intCast]
    linear_combination hsb' - (s : 𝓞 D.F) * ht
  · rw [map_mul, map_sub, map_intCast, map_intCast]
    linear_combination (s : 𝓞 D.F) ^ 2 * hc' - (s : 𝓞 D.F) ^ 2 * (ρ : 𝓞 D.F) * ht + (s : 𝓞 D.F) ^ 2 * hn

end GlobalTheory.UPel.HT.SplitIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitRatioGenericLineBundleIsos
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenIsoRatio

theorem gm_pullU_res {X Y : Scheme.{0}} (β : Y ⟶ X) (U : X.Opens) {V : Y.Opens} (h : V ≤ β ⁻¹ᵁ U) (y : Y)
    (hy : y ∈ V) (a : Γ(X, U)ˣ) : gm (𝟙 Y) y V (res h (pullU β U a)) = gm β y U a := by
  rw [gm_res (𝟙 Y) y h hy, gm_pull (𝟙 Y) β y U (h hy), Category.id_comp]

theorem gm_pull_g' {X Y : Scheme.{0}} (β : Y ⟶ X) (L : LB X) (y : Y) (i i' : L.ι) (hi : β y ∈ L.U i)
    (hi' : β y ∈ L.U i') :
    gm (𝟙 Y) y ((L.pull β).U (fun _ => i) ⊓ (L.pull β).U (fun _ => i'))
      ((L.pull β).g (fun _ => i) (fun _ => i')) = gm β y (L.U i ⊓ L.U i') (L.g i i') := by
  have hp : y ∈ (L.pull β).U (fun _ => i) ⊓ (L.pull β).U (fun _ => i') := ⟨mem_pull.2 hi, mem_pull.2 hi'⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU β _ (L.g i i'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hp _).trans ((gm_pull (𝟙 Y) β y (L.U i ⊓ L.U i') ⟨hi, hi'⟩ _).trans (by rw [Category.id_comp]))

theorem ratio : ∀ (X Y : Scheme.{0}) (β : Y ⟶ X) (P M : LB X) (N : LB Y), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull β) N) (w₁ : LB.Iso (P.pull β) N) (v : LB.Iso P M), w.IsGen → w₁.IsGen → v.IsGen → ∃ u : Γ(Y, ⊤)ˣ, ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ β ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (P.pull β).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.rs _ (le_top : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ ⊤) (u : Γ(Y, ⊤)) * (β.appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (M.pull β).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  intro X Y β P M N hP hM hN w w₁ v hw hw₁ hv
  let W : N.ι × P.ι × M.ι → Y.Opens := fun j =>
    N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1) ⊓ (M.pull β).U (fun _ => j.2.2)
  have l₁ : ∀ j, W j ≤ N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1) := fun j => inf_le_left
  have l₂ : ∀ j, W j ≤ N.U j.1 ⊓ (M.pull β).U (fun _ => j.2.2) := fun j =>
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have l₃ : ∀ j, W j ≤ β ⁻¹ᵁ (M.U j.2.2 ⊓ P.U j.2.1) := fun j y hy =>
    ⟨mem_pull.1 hy.2, mem_pull.1 hy.1.2⟩
  let r : ∀ j, Γ(Y, W j)ˣ := fun j =>
    res (l₁ j) (w₁.s (j.1, fun _ => j.2.1)) * (res (l₃ j) (pullU β _ (v.s (j.2.2, j.2.1))))⁻¹ *
      (res (l₂ j) (w.s (j.1, fun _ => j.2.2)))⁻¹
  have k : ∀ j (y : Y), y ∈ W j → gm (𝟙 Y) y (W j) (r j) =
      gm (𝟙 Y) y (N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1)) (w₁.s (j.1, fun _ => j.2.1)) *
        (gm β y (M.U j.2.2 ⊓ P.U j.2.1) (v.s (j.2.2, j.2.1)))⁻¹ *
        (gm (𝟙 Y) y (N.U j.1 ⊓ (M.pull β).U (fun _ => j.2.2)) (w.s (j.1, fun _ => j.2.2)))⁻¹ := by
    intro j y hy
    simp only [r, map_mul, map_inv]
    erw [gm_res (𝟙 Y) y (l₁ j) hy, gm_res (𝟙 Y) y (l₂ j) hy, gm_pullU_res β _ (l₃ j) y hy]
  obtain ⟨u, hu⟩ := glue_unit (⊤ : Y.Opens) W (fun _ => le_top)
    (fun y _ => by
      obtain ⟨n, hn⟩ := exists_chart hN y
      obtain ⟨i, hi⟩ := exists_chart hP (β y)
      obtain ⟨m, hm⟩ := exists_chart hM (β y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(n, i, m), ⟨hn, mem_pull.2 hi⟩, mem_pull.2 hm⟩) r
    (fun j j' y hy => by
      have hi := mem_pull.1 hy.1.1.2
      have hi' := mem_pull.1 hy.2.1.2
      have hm := mem_pull.1 hy.1.2
      have hm' := mem_pull.1 hy.2.2
      rw [k j y hy.1, k j' y hy.2,
        GlobalTheory.PartialCocycle.gm_iso hw₁ (𝟙 Y) y j.1 j'.1 (fun _ => j.2.1) (fun _ => j'.2.1) hy.1.1.1 hy.2.1.1
          hy.1.1.2 hy.2.1.2,
        GlobalTheory.PartialCocycle.gm_iso hw (𝟙 Y) y j.1 j'.1 (fun _ => j.2.2) (fun _ => j'.2.2) hy.1.1.1 hy.2.1.1
          hy.1.2 hy.2.2,
        GlobalTheory.PartialCocycle.gm_iso hv β y j.2.2 j'.2.2 j.2.1 j'.2.1 hm hm' hi hi',
        gm_pull_g' β P y _ _ hi hi', gm_pull_g' β M y _ _ hm hm']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨u, fun n i m hle => ?_⟩
  have e : res (l₁ (n, i, m)) (w₁.s (n, fun _ => i)) =
      res (le_top : W (n, i, m) ≤ ⊤) u * res hle (pullU β _ (v.s (m, i))) * res (l₂ (n, i, m)) (w.s (n, fun _ => m)) := by
    change _ = _ * res (l₃ (n, i, m)) (pullU β _ (v.s (m, i))) * _
    rw [hu (n, i, m)]
    simp only [r]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact congrArg Units.val e

end GlobalTheory.GenIsoRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeBaseChangeHomOfGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.GrpBC

theorem exists_baseChange_hom : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G A : Over S) [GrpObj G] [GrpObj A] (G' A' : Over S') [GrpObj G'] [GrpObj A'] (φG : G'.left ⟶ G.left) (φA : A'.left ⟶ A.left) (p : G ⟶ A), IsGrpPullback G' G f φG → IsGrpPullback A' A f φA → IsMonHom p → ∃ p' : G' ⟶ A', IsMonHom p' ∧ p'.left ≫ φA = φG ≫ p.left := by
  intro S S' f G A _ _ G' A' _ _ φG φA p hG hA hp
  have w : (φG ≫ p.left) ≫ A.hom = G'.hom ≫ f := by
    rw [Category.assoc, Over.w p, hG.1.w]
  have hq1 : hA.1.lift (φG ≫ p.left) G'.hom w ≫ φA = φG ≫ p.left := hA.1.lift_fst _ _ _
  have hq2 : hA.1.lift (φG ≫ p.left) G'.hom w ≫ A'.hom = G'.hom := hA.1.lift_snd _ _ _
  let p' : G' ⟶ A' := Over.homMk (hA.1.lift (φG ≫ p.left) G'.hom w) hq2
  have hp' : p'.left ≫ φA = φG ≫ p.left := hq1
  refine ⟨p', GlobalTheory.Serre.isMonHom_of_mul_comp p' fun T x y => ?_, hp'⟩
  apply Over.OverMorphism.ext
  apply hA.1.hom_ext
  · have e1 := hG.2 T x y (pushPt hG.1.w x) (pushPt hG.1.w y) rfl rfl
    have e2 := hA.2 T (x ≫ p') (y ≫ p') (pushPt hG.1.w x ≫ p) (pushPt hG.1.w y ≫ p)
      (by simp only [Over.comp_left, pushPt, Over.homMk_left, Category.assoc, hp'])
      (by simp only [Over.comp_left, pushPt, Over.homMk_left, Category.assoc, hp'])
    have e3 : (pushPt hG.1.w x ≫ p * pushPt hG.1.w y ≫ p).left = (x * y).left ≫ φG ≫ p.left := by
      rw [← MonObj.mul_comp, Over.comp_left, e1, Category.assoc]
    rw [← e2, e3, Over.comp_left, Category.assoc, hp']
  · rw [Over.w, Over.w]

end GlobalTheory.GrpBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeOfIsPullbackSpMap
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem exists_grpObj_isAbelianScheme_of_isPullback_spMap : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  intro R _ A _ g hA hg R' _ σ X' s' φ h
  have hsm : SmoothOfRelativeDimension g s' := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg
  let B := (Over.pullback (spMap σ)).obj A
  letI : GrpObj B := Functor.grpObjObj
  let e : B ≅ Over.mk s' := Over.isoMk h.isoPullback.symm (by simp [B])
  letI : GrpObj (Over.mk s') := GrpObj.ofIso e
  refine ⟨this, ?_, hsm⟩
  have hc := hA.comm
  have hcB : IsCommMonObj B := Functor.isCommMonObj_obj
  exact {
    comm := by
      constructor
      show (β_ _ _).hom ≫ ((e.inv ⊗ₘ e.inv) ≫ μ[B] ≫ e.hom) = (e.inv ⊗ₘ e.inv) ≫ μ[B] ≫ e.hom
      rw [← Category.assoc, ← BraidedCategory.braiding_naturality, Category.assoc,
        ← Category.assoc (β_ B B).hom, IsCommMonObj.mul_comm]
    smooth := MorphismProperty.of_isPullback (P := @Smooth) h hA.smooth
    proper := MorphismProperty.of_isPullback (P := @IsProper) h hA.proper
    geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h hA.geomConnected }

end GlobalTheory
end

