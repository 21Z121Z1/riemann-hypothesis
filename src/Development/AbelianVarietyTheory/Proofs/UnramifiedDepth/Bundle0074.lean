import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0070
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.CharacterGerms.RowTieTop
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetRingHomExistsUniqueSpec
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.JetEv

theorem prod_pow_mem_span_pow {A κ : Type} [CommRing A] [Fintype κ] (a : κ → A) (e : κ → ℕ) :
    ∏ i, a i ^ e i ∈ Ideal.span (Set.range a) ^ (∑ i, e i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

theorem jet_hom_spec : ∀ (V Ω A : Type) [CommRing V] [CommRing Ω] [CommRing A] [Algebra Ω A] (β : V →+* Ω) (κ : Type) [Fintype κ] [DecidableEq κ] (m : ℕ), (∀ a : κ → A, Ideal.span (Set.range a) ^ (m + 1) = ⊥ → ∃! ψ : Jet V κ m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) ∧ ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i) ∧ ∀ ψ : Jet V κ m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) → Ideal.span (Set.range fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) ^ (m + 1) = ⊥ ∧ (∀ i, IsNilpotent (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)))) ∧ ∀ f : MvPowerSeries κ V, ψ (psJet m f) = nEval (MvPowerSeries.map β f) (fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
  intro V Ω A _ _ _ _ β κ _ _ m
  refine ⟨fun a ha => ?_, fun ψ hψ => ?_⟩
  · letI : Algebra V A := ((algebraMap Ω A).comp β).toAlgebra
    let φ : Jet V κ m →ₐ[V] A := liftJet (MvPolynomial.aeval a) (by simpa using ha)
    have hφ : ∀ i, φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i := fun i =>
      MvPolynomial.aeval_X a i
    refine ⟨(φ : Jet V κ m →+* A), ⟨fun v => φ.commutes v, hφ⟩, ?_⟩
    rintro ψ ⟨h1, h2⟩
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun v => ?_) fun i => ?_)
    · exact (h1 v).trans (φ.commutes v).symm
    · exact (h2 i).trans (hφ i).symm
  · set a : κ → A := fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) with ha
    have h0 : Ideal.span (Set.range a) ^ (m + 1) = ⊥ := by
      have := map_orig_pow (ψ.comp (Ideal.Quotient.mk (orig V κ ^ (m + 1)))) (m + 1)
      rw [← Ideal.map_map, Ideal.map_quotient_self, Ideal.map_bot] at this
      exact this.symm
    have h1 : ∀ i, a i ^ (m + 1) = 0 := fun i => by
      have := Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i) : a i ∈ Ideal.span (Set.range a)) (m + 1)
      rwa [h0, Ideal.mem_bot] at this
    refine ⟨h0, fun i => ⟨m + 1, h1 i⟩, fun f => ?_⟩
    have hm : ∀ (e : κ →₀ ℕ) (c : V), ψ (Ideal.Quotient.mk _ (MvPolynomial.monomial e c)) =
        algebraMap Ω A (β c) * ∏ i, a i ^ e i := fun e c => by
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ← hψ]
      simp only [map_mul, map_prod, map_pow]
      rfl
    rw [GlobalTheory.evBasic_nEval_eq_tEval _ a (m + 1) h1, psJet, psTrunc, map_sum, map_sum]
    simp only [hm]
    rw [degLE, Finset.sum_filter, Finset.sum_image, ReciprocityTheory.PGsh.Be2.tEval]
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), MvPowerSeries.coeff_map]
      split_ifs with h
      · rfl
      · have h2 := prod_pow_mem_span_pow a fun i => (e i : ℕ)
        have h3 : m + 1 ≤ ∑ i, (e i : ℕ) := Nat.lt_of_not_le h
        have h4 := Ideal.pow_le_pow_right h3 h2
        rw [h0, Ideal.mem_bot] at h4
        rw [h4, mul_zero]
    · intro e _ e' _ h
      funext i
      exact Fin.ext (congrFun (Finsupp.equivFunOnFinite.symm.injective h) i)

end GlobalTheory.AlphaPair.JetEv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniversalChartPointsOverFieldPoint
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.JetUniv

open GlobalTheory.ChartBaseChange (fib fibLift fibFst fibSnd fib_cond fib_ker exists_pt_of_aug pt_eps_self)

def unitSec {S : Scheme.{0}} (G : Over S) [GrpObj G] : S ⟶ G.left := (η[G]).left

def lft {S T : Scheme.{0}} {G : Over S} {f : T ⟶ S} (y : Over.mk f ⟶ G) : T ⟶ G.left := y.left

theorem lft_w {S T : Scheme.{0}} {G : Over S} {f : T ⟶ S} (y : Over.mk f ⟶ G) : lft y ≫ G.hom = f := Over.w y

theorem lft_inj {S T : Scheme.{0}} {G : Over S} {f : T ⟶ S} {y z : Over.mk f ⟶ G} (h : lft y = lft z) : y = z :=
  Over.OverMorphism.ext h

theorem unitSec_w {S : Scheme.{0}} (G : Over S) [GrpObj G] : unitSec G ≫ G.hom = 𝟙 S := Over.w (η[G])

theorem eq_one_iff {S T : Scheme.{0}} {G : Over S} [GrpObj G] {f : T ⟶ S} (y : Over.mk f ⟶ G) :
    y = 1 ↔ lft y = f ≫ unitSec G := by
  have e : lft (1 : Over.mk f ⟶ G) = f ≫ unitSec G := by
    show (toUnit (Over.mk f) ≫ η[G]).left = _
    rw [Over.comp_left, Over.toUnit_left]
    rfl
  exact ⟨fun h => h ▸ e, fun h => lft_inj (h.trans e.symm)⟩

variable {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] {κ : Type}

theorem aug_X (m : ℕ) (i : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X i) = 0
  simp

theorem ker_aug_pow (m : ℕ) : RingHom.ker (jetAug : Jet V κ m →ₐ[V] V) ^ (m + 1) = ⊥ := by
  have hle : RingHom.ker (jetAug : Jet V κ m →ₐ[V] V) ≤ (orig V κ).map (Ideal.Quotient.mk _) := fun z hz => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h0 : MvPolynomial.aeval (fun _ : κ => (0 : V)) p = 0 := hz
    have h1 : MvPolynomial.constantCoeff p = 0 := by simpa using h0
    have h2 := sub_const_mem_orig p
    rw [h1, map_zero, sub_zero] at h2
    exact Ideal.mem_map_of_mem _ h2
  rw [eq_bot_iff]
  refine (Ideal.pow_right_mono hle _).trans ?_
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

def toSp {A : Type} [CommRing A] [Algebra V A] (y : overAt (𝟙 (Sp V)) A ⟶ G) : Chart.sp (R₀ := V) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _))

def ofSp {A : Type} [CommRing A] [Algebra V A] (y : Chart.sp (R₀ := V) A ⟶ G) : overAt (𝟙 (Sp V)) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _).symm)

theorem one_at_iff {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B)
    (y : overAt (𝟙 (Sp V)) A ⟶ G) : homAt (𝟙 (Sp V)) f ≫ y = 1 ↔ Chart.spMap f ≫ toSp y = 1 := by
  rw [eq_one_iff, eq_one_iff]
  have e : (spMap (algebraMap V B) ≫ 𝟙 (Sp V)) ≫ unitSec G = spMap (algebraMap V B) ≫ unitSec G := by
    rw [Category.comp_id]
  rw [e]
  rfl

theorem univ_over [IsLocalRing V] {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x)
    {A Ω : Type} [CommRing A] [Algebra V A] [CommRing Ω] [Algebra V Ω] (q : A →ₐ[V] Ω) (hq : Function.Surjective q)
    {m : ℕ} (hJ : RingHom.ker q ^ (m + 1) = ⊥) (y : Chart.sp (R₀ := V) A ⟶ G) (hy : Chart.spMap q ≫ y = 1) :
    ∃! ψ : Jet V κ m →ₐ[V] A, (∀ i, q (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) = 0) ∧
      y.left = spMap (ψ : Jet V κ m →+* A) ≫ (x m).left := by
  obtain ⟨C⟩ := Chart.exists_chart G
  obtain ⟨h, hh, hqh⟩ := exists_pt_of_aug C q hq hJ y hy
  obtain ⟨k, hk, hqk⟩ := exists_pt_of_aug C (jetAug : Jet V κ m →ₐ[V] V)
    (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩) (ker_aug_pow m) (toSp (x m)) ((one_at_iff _ _).1 (hx.2.1 m))
  have hk' : (x m).left = (Chart.pt C k).left := congrArg CommaMorphism.left hk
  have mv : ∀ {B : Type} [CommRing B] [Algebra V B] (v : Jet V κ m →ₐ[V] B),
      spMap (v : Jet V κ m →+* B) ≫ (x m).left = (Chart.pt C (v.comp k)).left := by
    intro B _ _ v
    rw [hk', ← Chart.spMap_pt]
    rfl
  let h₀ := fibLift q (Chart.eps C) h hqh
  obtain ⟨ψ₀, ⟨ha, hψ₀⟩, hu⟩ := hx.2.2 (fib q) (fibFst q) m (fib_ker q hJ) (ofSp (Chart.pt C h₀)) (by
    rw [one_at_iff]
    show Chart.spMap _ ≫ Chart.pt C h₀ = 1
    rw [Chart.spMap_pt]
    exact pt_eps_self C)
  have h0 : h₀ = ψ₀.comp k :=
    Chart.pt_injective C (Over.OverMorphism.ext ((congrArg CommaMorphism.left hψ₀).trans (mv ψ₀)))
  refine ⟨(fibSnd q).comp ψ₀, ⟨fun i => ?_, ?_⟩, ?_⟩
  · rw [AlgHom.comp_apply, fib_cond, ← AlgHom.comp_apply (fibFst q), ha, aug_X, map_zero]
  · rw [mv, AlgHom.comp_assoc, ← h0, hh]
    rfl
  · rintro v ⟨hv0, hv1⟩
    have hv : q.comp v = (Algebra.ofId V Ω).comp jetAug :=
      Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jet_hom_ext fun i => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, hv0, aug_X, map_zero]
    have hvk : h = v.comp k :=
      Chart.pt_injective C (Over.OverMorphism.ext ((congrArg CommaMorphism.left hh).symm.trans (hv1.trans (mv v))))
    have e := hu (fibLift q jetAug v hv) ⟨rfl, Over.OverMorphism.ext (by
      refine Eq.trans ?_ (mv _).symm
      show (Chart.pt C h₀).left = _
      congr 2
      refine AlgHom.ext fun s => Subtype.ext (Prod.ext ?_ ?_)
      · exact (AlgHom.congr_fun hqk s).symm
      · exact AlgHom.congr_fun hvk s)⟩
    rw [← e]
    rfl

theorem univ_left [IsLocalRing V] {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x)
    {A Ω : Type} [CommRing A] [Algebra V A] [CommRing Ω] [Algebra V Ω] (q : A →ₐ[V] Ω) (hq : Function.Surjective q)
    {m : ℕ} (hJ : RingHom.ker q ^ (m + 1) = ⊥) (y : Sp A ⟶ G.left) (hw : y ≫ G.hom = spMap (algebraMap V A))
    (hy : spMap (q : A →+* Ω) ≫ y = spMap (algebraMap V Ω) ≫ unitSec G) :
    ∃! ψ : Jet V κ m →ₐ[V] A, (∀ i, q (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) = 0) ∧
      y = spMap (ψ : Jet V κ m →+* A) ≫ lft (x m) :=
  univ_over hx q hq hJ (Over.homMk y hw) ((eq_one_iff _).2 hy)

theorem aug_left {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x) (A : Type) [CommRing A] [Algebra V A]
    (m : ℕ) : spMap (algebraMap V A) ≫ unitSec G =
      spMap (((Algebra.ofId V A).comp jetAug : Jet V κ m →ₐ[V] A) : Jet V κ m →+* A) ≫ lft (x m) := by
  have h2 : Chart.spMap ((Algebra.ofId V A).comp jetAug) ≫ toSp (x m) = 1 := by
    rw [← Chart.spMap_comp, Category.assoc, (one_at_iff _ _).1 (hx.2.1 m), MonObj.comp_one]
  exact ((eq_one_iff _).1 h2).symm

section Field

variable {Ω : Type} [Field Ω] [Algebra V Ω] {A : Type} [CommRing A] [Algebra Ω A] [Algebra V A] [IsScalarTower V Ω A]

theorem hom_eq : spMap (algebraMap Ω A) ≫ spMap (algebraMap V Ω) = spMap (algebraMap V A) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

theorem exists_jetHom {B : Type} [CommRing B] [Algebra V B] {m : ℕ} {I : Ideal B} (hI : I ^ (m + 1) = ⊥) (a : κ → B)
    (ha : ∀ i, a i ∈ I) : ∃ ψ : Jet V κ m →ₐ[V] B, ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i :=
  ⟨liftJet (MvPolynomial.aeval a) (by
      rw [eq_bot_iff, ← hI]
      refine Ideal.pow_right_mono (Ideal.span_le.2 ?_) _
      rintro _ ⟨i, rfl⟩
      simpa using ha i), fun i => MvPolynomial.aeval_X a i⟩

theorem universalJetCoordinates_points_over_field [IsLocalRing V] {d : ℕ} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G}
    (hx : GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x) {P : PtFam (spMap (algebraMap V Ω)) G d}
    (hP : IsJetPt (algebraMap V Ω) x P) (π : A →ₐ[Ω] Ω) (hπ : IsNilpotent (RingHom.ker π)) :
    (∀ a : Fin d → A, (∀ j, IsNilpotent (a j)) → P A a = 1 → a = 0) ∧
    ∀ z : overAt (spMap (algebraMap V Ω)) A ⟶ G, homAt _ π ≫ z = 1 →
      ∃ a : Fin d → A, (∀ j, IsNilpotent (a j)) ∧ P A a = z := by
  have hq : Function.Surjective (π.restrictScalars V) := fun r => ⟨algebraMap Ω A r, π.commutes r⟩
  obtain ⟨m, hm⟩ := hπ
  have hJ : RingHom.ker (π.restrictScalars V) ^ (m + 1) = ⊥ := by
    show RingHom.ker π ^ (m + 1) = ⊥
    rw [pow_succ, hm, zero_mul]
    rfl
  have hP' : ∀ ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] A,
      lft (P A fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))) =
        spMap (ψ : Jet V (Fin 1 × Fin d) m →+* A) ≫ lft (x m) := fun ψ =>
    hP A m (ψ : Jet V (Fin 1 × Fin d) m →+* A) fun v =>
      (ψ.commutes v).trans (IsScalarTower.algebraMap_apply V Ω A v)
  refine ⟨fun a ha h1 => ?_, fun z hz => ?_⟩
  · have ha0 : ∀ j, π.restrictScalars V (a j) = 0 := fun j => ((ha j).map (π.restrictScalars V)).eq_zero
    obtain ⟨ψ, hψ⟩ := exists_jetHom (V := V) hJ (fun p : Fin 1 × Fin d => a p.2) fun p => ha0 p.2
    have hl := hP' ψ
    rw [show (fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))) = a from funext fun j => hψ _,
      (eq_one_iff _).1 h1, hom_eq] at hl
    have e := (univ_left hx _ hq hJ (spMap (algebraMap V A) ≫ unitSec G)
      (by rw [Category.assoc, unitSec_w, Category.comp_id])
      (by rw [← Category.assoc, spMap_comp_alg])).unique (y₁ := ψ)
      (y₂ := (Algebra.ofId V A).comp jetAug) ⟨fun i => by rw [hψ, ha0], hl⟩
      ⟨fun i => by rw [AlgHom.comp_apply, aug_X, map_zero, map_zero], aug_left hx A m⟩
    funext j
    have h3 := hψ (0, j)
    rw [e, AlgHom.comp_apply, aug_X, map_zero] at h3
    exact h3.symm
  · obtain ⟨ψ, ⟨h0, h1⟩, -⟩ := univ_left hx _ hq hJ (lft z) ((lft_w z).trans hom_eq) (by
      have h3 : spMap (π : A →+* Ω) ≫ lft z = _ := (eq_one_iff _).1 hz
      rw [hom_eq (A := Ω)] at h3
      exact h3)
    refine ⟨fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X (0, j))), fun j => ⟨m + 1, ?_⟩,
      lft_inj ((hP' ψ).trans h1.symm)⟩
    have := Ideal.pow_mem_pow (RingHom.mem_ker.2 (h0 (0, j))) (m + 1)
    rwa [hJ, Ideal.mem_bot] at this

end Field

end GlobalTheory.AlphaPair.JetUniv

namespace GlobalTheory.AlphaPair

theorem jetUniv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω) (P : PtFam (spMap β) t.G d), IsJetPt β x P → IsPtUniv (spMap β) t.G P := by
  intro E _ _ _ H V _ _ t d x hx Ω _ β P hP A _ _ π hπ
  letI : Algebra V Ω := β.toAlgebra
  letI : Algebra V A := ((algebraMap Ω A).comp β).toAlgebra
  haveI : IsScalarTower V Ω A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact JetUniv.universalJetCoordinates_points_over_field hx hP π hπ

end GlobalTheory.AlphaPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationIntegersPadicComplete
section
open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.ValExp

noncomputable def halfPow (t : WithTop ℝ) : NNReal :=
  WithTop.recTopCoe (0 : NNReal) (fun r : ℝ => (2⁻¹ : NNReal) ^ r) t

theorem halfPow_top : halfPow ⊤ = 0 := rfl

theorem halfPow_coe (r : ℝ) : halfPow (r : WithTop ℝ) = (2⁻¹ : NNReal) ^ r := rfl

theorem halfPow_zero : halfPow 0 = 1 := by
  rw [← WithTop.coe_zero, halfPow_coe, NNReal.rpow_zero]

theorem halfPow_one : halfPow 1 = 2⁻¹ := by
  rw [← WithTop.coe_one, halfPow_coe, NNReal.rpow_one]

theorem halfPow_add (a b : WithTop ℝ) : halfPow (a + b) = halfPow a * halfPow b := by
  induction a using WithTop.recTopCoe with
  | top => simp [halfPow_top]
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp [halfPow_top]
    | coe b => rw [← WithTop.coe_add, halfPow_coe, halfPow_coe, halfPow_coe, NNReal.rpow_add (by norm_num)]

theorem halfPow_strictAnti : StrictAnti halfPow := by
  intro a b hab
  induction a using WithTop.recTopCoe with
  | top => exact absurd hab not_top_lt
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => rw [halfPow_top, halfPow_coe]; exact NNReal.rpow_pos (by norm_num)
    | coe b =>
      rw [halfPow_coe, halfPow_coe]
      exact NNReal.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) (by exact_mod_cast hab)

variable {C : Type} [Field C]

noncomputable def mulVal (V : VF C) : Valuation C NNReal where
  toFun x := halfPow (V.v x)
  map_zero' := by rw [V.v.map_zero, halfPow_top]
  map_one' := by rw [V.v.map_one, halfPow_zero]
  map_mul' x y := by rw [V.v.map_mul, halfPow_add]
  map_add_le_max' x y := by
    refine (halfPow_strictAnti.antitone (V.v.map_add x y)).trans ?_
    rcases le_total (V.v x) (V.v y) with h | h
    · rw [min_eq_left h]; exact le_max_left _ _
    · rw [min_eq_right h]; exact le_max_right _ _

theorem mulVal_apply (V : VF C) (x : C) : mulVal V x = halfPow (V.v x) := rfl

theorem mulVal_l (V : VF C) : mulVal V (V.l : C) = 2⁻¹ := by
  rw [mulVal_apply, V.v_l, halfPow_one]

theorem mulVal_le_one_iff (V : VF C) (x : C) : mulVal V x ≤ 1 ↔ V.Ge 0 x := by
  rw [mulVal_apply, ← halfPow_zero, halfPow_strictAnti.le_iff_ge]; rfl

theorem mulVal_lt_one_iff (V : VF C) (x : C) : mulVal V x < 1 ↔ V.MM x := by
  rw [mulVal_apply, ← halfPow_zero, halfPow_strictAnti.lt_iff_gt]; rfl

theorem ge_l_pow (V : VF C) (n : ℕ) : V.Ge n ((V.l : C) ^ n) := by
  induction n with
  | zero => simpa using VF.Ge.one
  | succ n ih => rw [pow_succ]; push_cast; exact ih.mul VF.ge_l

theorem ge_of_l_pow_mul (V : VF C) (n : ℕ) {w : ℝ} {a : C} (h : V.Ge w ((V.l : C) ^ n * a)) :
    V.Ge (w - n) a := by
  induction n generalizing w with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', mul_assoc] at h
    refine (ih h.of_l_mul).mono (le_of_eq ?_)
    push_cast; ring

theorem mem_pow_iff (V : VF C) (n : ℕ) (x : (mulVal V).integer) :
    x ∈ (Ideal.span {((V.l : ℕ) : (mulVal V).integer)} ^ n • ⊤ :
      Submodule (mulVal V).integer (mulVal V).integer) ↔ V.Ge n (x : C) := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : V.Ge 0 (y : C) := (mulVal_le_one_iff V _).1 y.2
    simpa using (ge_l_pow V n).mul hy
  · intro h
    have hl : (V.l : C) ^ n ≠ 0 := pow_ne_zero _ VF.l_ne_zero
    have hy : V.Ge 0 (((V.l : C) ^ n)⁻¹ * x) := by
      have := ge_of_l_pow_mul V n (w := n) (a := ((V.l : C) ^ n)⁻¹ * x)
        (by rwa [mul_inv_cancel_left₀ hl])
      simpa using this
    refine ⟨⟨_, (mulVal_le_one_iff V _).2 hy⟩, Subtype.ext ?_⟩
    simp [mul_inv_cancel_left₀ hl]

theorem isAdicComplete (V : VF C)
    (hc : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) :
    IsAdicComplete (Ideal.span {((V.l : ℕ) : (mulVal V).integer)}) (mulVal V).integer where
  haus' x hx := by
    by_contra h0
    have h1 : (x : C) ≠ 0 := fun h => h0 (Subtype.ext h)
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff V.v).2 h1)
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have := (mem_pow_iff V n x).1 (SModEq.zero.1 (hx n))
    rw [VF.Ge, ← ht] at this
    exact hn.not_ge (by exact_mod_cast this)
  prec' f hf := by
    obtain ⟨x, hx⟩ := hc (fun n => (f n : C)) fun n => by
      have := (mem_pow_iff V n _).1 (SModEq.sub_mem.1 (hf (Nat.le_succ n)).symm)
      simpa using this
    have h0 : V.Ge 0 x := by
      have h1 : V.Ge 0 (x - f 0) := by simpa using hx 0
      simpa using h1.add ((mulVal_le_one_iff V _).1 (f 0).2)
    refine ⟨⟨x, (mulVal_le_one_iff V _).2 h0⟩, fun n => SModEq.symm (SModEq.sub_mem.2 ?_)⟩
    rw [mem_pow_iff]
    simpa using hx n

theorem exists_mulVal : ∀ (C : Type) [Field C] (V : VF C) [Fact V.l.Prime], (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → ∃ vm : Valuation C NNReal, ValuationFitting.ValTie V vm ∧ 0 < (vm (V.l : C) : ℝ) ∧ (vm (V.l : C) : ℝ) < 1 ∧ (∀ x : C, vm x ≤ 1 ↔ V.Ge 0 x) ∧ (∀ x : C, vm x < 1 ↔ V.MM x) ∧ IsAdicComplete (Ideal.span {((V.l : ℕ) : vm.integer)}) vm.integer ∧ Nonempty (Algebra ℤ_[V.l] vm.integer) := by
  intro C _ V _ hc
  haveI := isAdicComplete V hc
  refine ⟨mulVal V, fun x hx => ?_, ?_, ?_, mulVal_le_one_iff V, mulVal_lt_one_iff V, this, ?_⟩
  · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff V.v).2 hx)
    refine ⟨t, ht.symm, ?_⟩
    rw [mulVal_l, mulVal_apply, ← ht, halfPow_coe, NNReal.coe_rpow]
  · rw [mulVal_l]; norm_num
  · rw [mulVal_l]; norm_num
  · obtain ⟨φ⟩ := nonempty_padicInt_ringHom_of_isAdicComplete
      (Ideal.span {((V.l : ℕ) : (mulVal V).integer)}) V.l (Ideal.mem_span_singleton_self _)
    exact ⟨φ.toAlgebra⟩

end GlobalTheory.ValExp
end

