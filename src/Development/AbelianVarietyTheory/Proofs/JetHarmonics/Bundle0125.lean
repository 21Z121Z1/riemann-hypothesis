import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.DualLattices.Bundle0016
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0007
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotIsUnitNatCastOfIsLocalHom
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0027
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0033
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0048
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0121
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasFinColengthOfHasLen
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.PGsh.Up
open GlobalTheory.IndefiniteRowSideFullHecke.LieMatrixCoordinates GlobalTheory.TorsionCompare NumberField
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AvChartCompare

section Charts

variable {R : Type} [CommRing R]

variable {G : Over (Sp R)} {d : ℕ}

end Charts

section Series

variable {O : Type} [CommRing O] {d : ℕ}

variable {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C]

def HasFinColength (F : Fin d → PS O 2 d) {s : ℕ} (u : Fin s → Fin d → O) (x : NNReal) : Prop :=
  ∃ S : Set (PS O 1 d), S.Finite ∧ (∀ χ ∈ S, IsMultSeries F χ) ∧
    HasLen v O ((Fin s → O) ⧸
      Submodule.span O {l | ∃ χ ∈ S, l = fun i => linCoeff χ ⬝ᵥ u i}) x

variable {v}

theorem hasLen_le_of_surjective (hv : v.Integers O) {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (π : M →ₗ[O] N) (hπ : Function.Surjective π) {x y : NNReal}
    (hx : HasLen v O M x) (hy : HasLen v O N y) : x ≤ y := by
  have := isLocal_of_integers hv
  obtain ⟨m, c, ⟨e⟩, rfl⟩ := hx
  obtain ⟨n, b, ⟨e'⟩, rfl⟩ := hy
  let f := e'.toLinearMap ∘ₗ π ∘ₗ e.symm.toLinearMap
  have hf : Function.Surjective f := e'.surjective.comp (hπ.comp e.symm.surjective)
  let q : Fin m → ((j : Fin n) → O ⧸ Ideal.span {b j}) :=
    fun i => f (Pi.single i (1 : O ⧸ Ideal.span {c i}))
  have hq : Submodule.span O (Set.range q) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨z, rfl⟩ := hf z
    have hz : z = ∑ i, (Quotient.out (z i) : O) • Pi.single i (1 : O ⧸ Ideal.span {c i}) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, _root_.mul_one,
          Ideal.Quotient.algebraMap_eq]
        exact (Ideal.Quotient.mk_out (z k)).symm
      · intro b _ hb
        simp [Pi.single_eq_of_ne' hb]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hz, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hT : ∀ k, ∑ i, (Matrix.diagonal c) k i • q i = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · simp only [Matrix.diagonal_apply_eq, q, ← map_smul]
      have : c k • (Pi.single k (1 : O ⧸ Ideal.span {c k}) : (i : Fin m) → O ⧸ Ideal.span {c i}) =
          0 := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, Algebra.smul_def, _root_.mul_one,
            Ideal.Quotient.algebraMap_eq]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
        · simp [Pi.single_eq_of_ne hj]
      rw [this, map_zero]
    · intro b _ hb; simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ k) h
  have h := det_mem_span_prod n b m q hq (Matrix.diagonal c) hT
  rw [Matrix.det_diagonal] at h
  simpa only [map_prod] using hv.le_of_dvd (Ideal.mem_span_singleton.1 h)

theorem HasFinColength.le (hv : v.Integers O) {F : Fin d → PS O 2 d} {s : ℕ}
    {u : Fin s → Fin d → O} {x y : NNReal} (hx : HasFinColength v F u x)
    (hy : HasLen v O ((Fin s → O) ⧸ dlogSpan F u) y) : x ≤ y := by
  obtain ⟨S, -, hS, hx⟩ := hx
  have hle : Submodule.span O {l | ∃ χ ∈ S, l = fun i => linCoeff χ ⬝ᵥ u i} ≤ dlogSpan F u :=
    Submodule.span_mono fun l ⟨χ, h, hl⟩ => ⟨χ, hS χ h, hl⟩
  exact hasLen_le_of_surjective hv (Submodule.factor hle) (Submodule.factor_surjective hle) hx hy

end Series

section Emb

variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

theorem exists_extend (τ : 𝓞 E →+* C) : ∃! σ : E →+* C, ∀ a : 𝓞 E, σ a = τ a := by
  have hτ : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h
    obtain ⟨n, hn⟩ := (Submodule.ne_bot_iff _).1
      (Ideal.IsIntegral.comap_ne_bot ℤ (I := RingHom.ker τ) h)
    have h1 : τ (algebraMap ℤ (𝓞 E) n) = 0 := hn.1
    simp [hn.2] at h1
  refine ⟨IsFractionRing.lift (K := E) hτ, fun a => IsFractionRing.lift_algebraMap hτ a,
    fun σ h => IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_⟩
  rw [IsFractionRing.lift_algebraMap]; exact h a

theorem exists_restrict (hv : v.Integers O) (σ : E →+* C) :
    ∃ τ : 𝓞 E →+* O, ∀ a : 𝓞 E, σ a = algebraMap O C (τ a) := by
  have h : ∀ a : 𝓞 E, ∃ z : O, algebraMap O C z = σ a := fun a => by
    have h1 : IsIntegral ℤ (σ a) := a.isIntegral_coe.map σ.toIntAlgHom
    exact hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h1.tower_top)
  choose f hf using h
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun a => (hf a).symm⟩ <;> intros <;> apply hv.hom_inj <;> simp [hf]

def embEquiv (hv : v.Integers O) : (𝓞 E →+* O) ≃ (E →+* C) :=
  Equiv.ofBijective (fun τ => (exists_extend ((algebraMap O C).comp τ)).choose) (by
    constructor
    · intro τ τ' h
      ext a
      apply hv.hom_inj
      have h1 := (exists_extend ((algebraMap O C).comp τ)).choose_spec.1 a
      have h2 := (exists_extend ((algebraMap O C).comp τ')).choose_spec.1 a
      exact h1.symm.trans ((DFunLike.congr_fun h (a : E)).trans h2)
    · intro σ
      obtain ⟨τ, hτ⟩ := exists_restrict hv σ
      exact ⟨τ, ((exists_extend ((algebraMap O C).comp τ)).choose_spec.2 σ hτ).symm⟩)

end Emb

section Places

variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)]
  {C : Type} [Field C] [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] O]

def Under (w : AvDefs.Place p (𝓞 E)) (P : Ideal (𝓞 E)) : Prop :=
  IsPrimeUnder (GlobalTheory.CutMultiplicationUnits.placeEquiv w).toPlace P

variable {w : AvDefs.Place p (𝓞 E)} {P : Ideal (𝓞 E)}

end Places

def AvAtCM (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T], ¬ IsUnit (p : T) →
    ∀ (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
      (D : DegData T (IsLocalRing.maximalIdeal T))
      (A : PolAV (Spec (CommRingCat.of (FractionRing T))))
      (U : UnifPre (IsLocalRing.maximalIdeal T) D A G)
      (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G),
      IsChartJ G F x →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
      (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) →
    ∀ [Module (𝓞 E) D.toPre.X] (io : RingAct G (𝓞 E))
      (oD : D.OAct (𝓞 E)) (oA : A.OAct (𝓞 E)), U.OLinear (𝓞 E) oD oA io →
    ∀ (act : Germ.OAct (𝓞 E) F), ChartActs G x io act →
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
      (O : Type) [CommRing O] [Algebra O C], v.Integers O →
      ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]
        (iota : T →+* O), IsLocalHom iota →
      ∀ (w : AvDefs.Place p (𝓞 E)) (t : Fin w.n ≃ AvDefs.Emb (O := O) w.e) (vd : ℝ),
        AvDefs.HasVd p v w t vd →
      ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O),
        (∀ j, IsEigBasis (actMap iota act) ((t j : AvDefs.Emb (O := O) w.e) : 𝓞 E →+* O) (W j)) →
        (∀ τ ∈ AvDefs.Emb (O := O) w.bar,
          ∃ W' : Fin rm → Fin d → O, IsEigBasis (actMap iota act) τ W') →
      ∃ xs : Fin w.n → NNReal, (∀ j, HasAF v (F.mapF iota) (W j) (xs j)) ∧
        v (algebraMap O C (p : O)) ^ ((w.n : ℝ) * rm * (1 / ((p : ℝ) - 1) + vd / 2)) ≤ ∏ j, xs j

abbrev Conclusion : Type 1 :=
  ∀ {T : Type} [CommRing T] {E : Type} [Field E] [NumberField E] {d : ℕ} (_F : FGLaw T d)
    {C : Type} [Field C] [CharZero C] (_v : Valuation C NNReal) {O : Type} [CommRing O]
    [Algebra O C] (_io : T →+* O) (_w : Ideal (𝓞 E)) {rp : ℕ} (_rm : ℕ)
    (_u : (E →+* C) → Fin rp → Fin d → O), Prop

def OverCharts (p : ℕ) [Fact p.Prime] (Q : Conclusion) : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T], ¬ IsUnit (p : T) →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) →
  ∀ (D : DegData T (IsLocalRing.maximalIdeal T)) [Module (𝓞 E) D.toPre.X]
    (A : PolAV (Spec (CommRingCat.of (FractionRing T))))
    (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (IsLocalRing.maximalIdeal T) D A G)
    (ιD : D.OAct (𝓞 E)) (ιA : A.OAct (𝓞 E)) (ιG : RingAct G (𝓞 E)),
    U.OLinear (𝓞 E) ιD ιA ιG →
  ∀ (d : ℕ) (x : JetFam G d) (F : FGLaw T d) (α : Germ.OAct (𝓞 E) F),
    IsJetChart G x → IsLawOf G x F → IsActOf G x ιG α →
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [IsAdicComplete (Ideal.span {(p : O)}) O],
    v.Integers O →
  ∀ (io : T →+* O), IsLocalHom io →
  ∀ (w : Ideal (𝓞 E)), w.IsPrime → (p : 𝓞 E) ∈ w → w ≠ w.comap (starRingEnd (𝓞 E)) →
  ∀ (rp rm : ℕ) (u : (E →+* C) → Fin rp → Fin d → O) (u' : (E →+* C) → Fin rm → Fin d → O),
    (∀ τ, Induces v τ w → IsEigenBasis α io τ (u τ)) →
    (∀ σ, Induces v σ (w.comap (starRingEnd (𝓞 E))) → IsEigenBasis α io σ (u' σ)) →
    Q F v io w rm u

def bound_vp (p : ℕ) {E : Type} [Field E] [NumberField E] (w : Ideal (𝓞 E)) (r : ℝ) : ℝ :=
  (localDeg p w : ℝ) * r * (1 / ((p : ℝ) - 1) + vd_vp p w / 2)

def ColengthsExist (p : ℕ) : Conclusion := fun {_} _ {_} _ _ {_} F {_} _ _ v {_} _ _ io w {_} _ u =>
  ∀ τ, Induces v τ w → ∃ a : ℝ, HasColength_vp p v F io (u τ) a

open Classical in

def ColengthsBounded (p : ℕ) : Conclusion :=
  fun {_} _ {E} _ _ {_} F {C} _ _ v {_} _ _ io w {_} rm u =>
  ∀ a : (E →+* C) → ℝ, (∀ τ, Induces v τ w → HasColength_vp p v F io (u τ) (a τ)) →
    ∑ τ ∈ Finset.univ.filter (fun τ : E →+* C => Induces v τ w), a τ ≤ bound_vp p w rm

open Classical in

def FiniteColengthsBounded (p : ℕ) : Conclusion :=
  fun {_} _ {E} _ _ {_} F {C} _ _ v {_} _ _ io w {_} rm u =>
  ∃ xs : (E →+* C) → NNReal, (∀ τ, Induces v τ w → HasFinColength v (F.mapF io) (u τ) (xs τ)) ∧
    v (p : C) ^ bound_vp p w rm ≤
      ∏ τ ∈ Finset.univ.filter (fun τ : E →+* C => Induces v τ w), xs τ

end GlobalTheory.AvChartCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeValueLePlanBlocks
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators

namespace GlobalTheory.PlanValue

theorem bg_add {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) (i : ℕ) (hi : Odd i) :
    RF.bg (a + (i : ZMod d)) = 1 - RF.bg a := by
  have h : Even (a + (i : ZMod d)).val ↔ ¬ Even a.val := by
    rw [ZMod.val_add, ZMod.val_natCast, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ hd.two_dvd, Nat.add_mod,
      Nat.mod_mod_of_dvd _ hd.two_dvd, Nat.odd_iff.1 hi]
    omega
  unfold RF.bg
  by_cases ha : Even a.val
  · rw [if_pos ha, if_neg (by rw [h]; simpa using ha)]; rfl
  · rw [if_neg ha, if_pos (h.2 ha)]; rfl

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem big_bg (X : RowData C V d I J) (h : X.Alt) (a : ZMod d) : X.big (RF.bg a) a := by
  unfold RF.bg
  split_ifs with ha
  · exact (h.2 a).2 ha
  · exact (X.big_compl 0 a).2 fun hb => ha ((h.2 a).1 hb)

theorem rk_le (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) : X.rkF g a ≤ X.n + (X.j + X.j') := by
  by_cases h : X.big g a
  · have : X.rkF g a = _ := X.rk_big g a h
    omega
  · have : X.rkF g a = _ := X.rk_small g a h
    omega

def rst (n : ℕ) (ga : Fin 2 → ZMod d → ℕ → ℕ) (g : Fin 2) (a : ZMod d) (k : ℕ) : ℕ :=
  if g = RF.bg a ∧ k = n then 0 else ga g a k

theorem deg_le (X : RowData C V d I J) (n K : ℕ) (ga : Fin 2 → ZMod d → ℕ → ℕ) :
    RF.monDegAll X 0 (rst n ga 0) K + RF.monDegAll X 1 (rst n ga 1) K ≤ RF.restDeg RF.bg n ga K := by
  have key : ∀ g, RF.monDegAll X g (rst n ga g) K ≤
      ∑ a : ZMod d, ∑ k ∈ Finset.Icc 1 K, if g = RF.bg a ∧ k = n then 0 else k * ga g a k := by
    intro g
    unfold RF.monDegAll monDeg
    refine Finset.sum_le_sum (N := ℕ) fun a _ => ?_
    refine le_trans (Finset.sum_le_sum_of_subset (M := ℕ)
      (Finset.Icc_subset_Icc_right (min_le_left K _))) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold rst
    split_ifs <;> simp
  unfold RF.restDeg
  rw [Fin.sum_univ_two]
  convert Nat.add_le_add (key 0) (key 1)

noncomputable def supp {l : ℕ} {W : ZMod d → ℕ} (p : Plan l d W) : Finset (ZMod d × ℕ) :=
  (Finset.univ ×ˢ oddLevels d).filter fun x => p.y x.1 x.2 ≠ 0

theorem sum_supp {M : Type} [AddCommMonoid M] {l : ℕ} {W : ZMod d → ℕ} (p : Plan l d W) (f : ZMod d → ℕ → ℕ → M)
    (hf : ∀ a i, f a i 0 = 0) :
    ∑ x ∈ supp p, f x.1 x.2 (p.y x.1 x.2) = ∑ a, ∑ i ∈ oddLevels d, f a i (p.y a i) := by
  rw [← Finset.sum_product']
  unfold supp
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with h
  · rfl
  · rw [not_not.1 h, hf]

theorem card_supp {l : ℕ} {W : ZMod d → ℕ} (p : Plan l d W) (N : ℕ) (h : ∀ a i, N ≤ i → p.y a i = 0) :
    (supp p).card ≤ d * (N - 1) := by
  have : supp p ⊆ Finset.univ ×ˢ Finset.Ico 1 N := by
    intro x hx
    simp only [supp, oddLevels, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Ico]
    refine ⟨hx.1.2.pos, ?_⟩
    by_contra hc
    exact hx.2 (h _ _ (not_lt.1 hc))
  simpa [ZMod.card] using Finset.card_le_card this

noncomputable def blocks {W : ZMod d → ℕ} (X : RowData C V d I J) (p : Plan V.l d W) (ga : Fin 2 → ZMod d → ℕ → ℕ)
    (K : ℕ) : List (RF.GlobalTheory d × ℝ) :=
  (RF.GlobalTheory.mon 0 (rst X.n ga 0) K, (RF.monDegAll X 0 (rst X.n ga 0) K : ℝ) / ((V.l : ℝ) - 1)) ::
  (RF.GlobalTheory.mon 1 (rst X.n ga 1) K, (RF.monDegAll X 1 (rst X.n ga 1) K : ℝ) / ((V.l : ℝ) - 1)) ::
  (((Finset.univ : Finset (ZMod d)).toList.map fun a =>
      (RF.GlobalTheory.ch (RF.bg a) a (p.u a), RF.chBd V.l X.n X.m (p.u a))) ++
    ((supp p).toList.map fun x =>
      (RF.GlobalTheory.bi (RF.bg x.1) x.1 x.2 (p.y x.1 x.2), RF.blockBd V.l X.n X.m x.2 (p.y x.1 x.2))))

theorem blocks_rows {W : ZMod d → ℕ} (X : RowData C V d I J) (p : Plan V.l d W) (ga : Fin 2 → ZMod d → ℕ → ℕ)
    (K N : ℕ) (hN : 1 ≤ N) (h : ∀ a i, N ≤ i → p.y a i = 0) :
    ((blocks X p ga K).map fun q => q.1.what₂ X.n).sum ≤ d * (N * X.n) + 2 * K := by
  simp only [blocks, List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_map,
    Finset.sum_map_toList, Function.comp_def, RF.GlobalTheory.what₂, Finset.sum_const, smul_eq_mul, Finset.card_univ, ZMod.card]
  have h1 := Nat.mul_le_mul_right X.n (card_supp p N h)
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h1
  nlinarith

theorem blocks_bd {W : ZMod d → ℕ} (X : RowData C V d I J) (p : Plan V.l d W) (ga : Fin 2 → ZMod d → ℕ → ℕ)
    (K : ℕ) (hl : 2 ≤ V.l) :
    ((blocks X p ga K).map Prod.snd).sum ≤
      p.bound X.n X.m + (RF.restDeg RF.bg X.n ga K : ℝ) / ((V.l : ℝ) - 1) := by
  have hl' : (0 : ℝ) < (V.l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ V.l := by exact_mod_cast hl
    linarith
  simp only [blocks, List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_map,
    Finset.sum_map_toList, Function.comp_def]
  rw [sum_supp p (fun _ i y => RF.blockBd V.l X.n X.m i y) (fun _ _ => by simp [RF.blockBd])]
  have h : ((RF.monDegAll X 0 (rst X.n ga 0) K : ℝ) + RF.monDegAll X 1 (rst X.n ga 1) K) ≤
      RF.restDeg RF.bg X.n ga K := by exact_mod_cast deg_le X X.n K ga
  have h' := div_le_div_of_nonneg_right h hl'.le
  rw [add_div] at h'
  have e : p.bound X.n X.m = (∑ a, ∑ i ∈ oddLevels d, RF.blockBd V.l X.n X.m i (p.y a i)) +
    ∑ a, RF.chBd V.l X.n X.m (p.u a) := rfl
  rw [e]
  linarith

theorem blocks_wt {W : ZMod d → ℕ} (X : RowData C V d I J) (hX : X.Alt) (p : Plan V.l d W)
    (ga : Fin 2 → ZMod d → ℕ → ℕ) (K : ℕ) (hK : X.n + (X.j + X.j') ≤ K)
    (hs : ∀ g a k, ga g a k ≠ 0 → 1 ≤ k ∧ k ≤ X.rkF g a) (hm : ∀ a, ga (RF.bg a) a X.n = W a)
    (g : Fin 2) (a : ZMod d) (k : ℕ) :
    ((blocks X p ga K).map fun q => q.1.wt X g a k).sum = ga g a k := by
  simp only [blocks, List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_map,
    Finset.sum_map_toList, Function.comp_def, RF.GlobalTheory.wt]
  rw [sum_supp p (fun b i y => (if g = RF.bg b ∧ a = b ∧ k = X.n then V.l ^ i * y else 0) +
    (if g = 1 - RF.bg b ∧ a = b + (i : ZMod d) ∧ k = X.n then y else 0)) (fun _ _ => by simp)]
  have hmon : ∀ g', (if g = g' ∧ 1 ≤ k ∧ k ≤ min K (X.rkF g' a) then rst X.n ga g' a k else 0) =
      if g = g' then rst X.n ga g a k else 0 := by
    intro g'
    by_cases hg : g = g'
    · subst hg
      have := rk_le X g a
      by_cases h0 : ga g a k = 0
      · simp [rst, h0]
      · have := hs g a k h0
        rw [if_pos ⟨rfl, by omega, by omega⟩, if_pos rfl]
    · simp [hg]
  have hmon2 : (if g = 0 then rst X.n ga g a k else 0) + (if g = 1 then rst X.n ga g a k else 0) =
      rst X.n ga g a k := by fin_cases g <;> simp
  rw [hmon, hmon, ← add_assoc, hmon2]
  have h2 : ∑ b, ∑ i ∈ oddLevels d, (if g = 1 - RF.bg b ∧ a = b + (i : ZMod d) ∧ k = X.n then p.y b i else 0) =
      ∑ i ∈ oddLevels d, if g = RF.bg a ∧ k = X.n then p.y (a - (i : ZMod d)) i else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : Odd i := (Finset.mem_filter.1 hi).2
    rw [Finset.sum_eq_single (a - (i : ZMod d))]
    · rw [← bg_add hX.1 _ i hi']; simp
    · intro b _ hb
      rw [if_neg]
      rintro ⟨-, h, -⟩
      exact hb (by rw [h]; simp)
    · simp
  have h1 : ∑ b, ∑ i ∈ oddLevels d, (if g = RF.bg b ∧ a = b ∧ k = X.n then V.l ^ i * p.y b i else 0) =
      ∑ i ∈ oddLevels d, if g = RF.bg a ∧ k = X.n then V.l ^ i * p.y a i else 0 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  have h3 : ∑ b, (if g = RF.bg b ∧ a = b ∧ k = X.n then p.u b else 0) =
      if g = RF.bg a ∧ k = X.n then p.u a else 0 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  simp only [Finset.sum_add_distrib]
  rw [h1, h2, h3]
  by_cases hc : g = RF.bg a ∧ k = X.n
  · obtain ⟨rfl, rfl⟩ := hc
    simp only [rst, and_self, if_true]
    rw [hm a, p.bal a]
    ring
  · simp [rst, hc]

theorem card_reps (P : RF.Par) (Z : Finset P.Pl) (h : RF.IsReps P Z) : Z.card * P.d = Fintype.card P.Pl := by
  classical
  rw [← Finset.card_univ]
  have : Z.card * P.d = (Z ×ˢ (Finset.univ : Finset (ZMod P.d))).card := by simp [ZMod.card]
  rw [this]
  refine Finset.card_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro p hp q hq hpq
    exact (h (P.pos q.1 q.2.val)).unique ⟨(Finset.mem_product.1 hp).1, hpq⟩
      ⟨(Finset.mem_product.1 hq).1, rfl⟩
  · intro z _
    obtain ⟨p, hp, -⟩ := h z
    exact ⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩

theorem val_le_plan : ∀ (P : RF.Par) (l : ℕ) (C1 : ℝ), ParOK P → 5 ≤ l → ∀ (Pk : RF.PkgInert P l C1) (p : ∀ z, Plan l P.d (RF.alongOrb P z Pk.W)),
    (∀ z ∈ Pk.Z, ∀ a i, i0 P.k l ≤ i → (p z).y a i = 0) →
    (∀ z ∈ Pk.Z, ∀ a i, (p z).y a i ≠ 0 → (RF.GlobalTheory.bi (RF.bg a) a i ((p z).y a i)).Attains (Pk.R.X z) (Pk.R.F z) (RF.blockBd l (P.k - 1) P.m i ((p z).y a i))) →
    Pk.ν ≤ (∑ z ∈ Pk.Z, (p z).bound (P.k - 1) P.m) + Pk.rest / ((l : ℝ) - 1) := by
  intro P l C1 hP hl Pk p hlev hatt
  obtain ⟨⟨C, V, hVl, I, J, X, F, hn⟩, Z, hZ, alt, ga, W, nW, T, θ0, rest, ν, wt, what₂, deg, val⟩ := Pk
  subst hVl
  dsimp only at *
  revert hlev hatt
  revert p
  change ∀ p : ∀ z, Plan V.l P.d (RF.alongOrb P z W), _
  intro p hlev hatt
  have hk := hP.mk_le
  have hi0 : 1 ≤ i0 P.k V.l := by
    have := (GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 P.k V.l (by omega) (by omega)).2.1
    omega
  have key := val (fun z => blocks (X z) (p z) (ga z) P.r) ?_ ?_ ?_
  · refine key.trans ?_
    rw [wt.rest_eq, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z _ => ?_
    have := blocks_bd (X z) (p z) (ga z) P.r (by omega)
    rw [(hn z).1, (hn z).2] at this
    simpa using this
  · intro z hz q hq
    simp only [blocks, List.mem_cons, List.mem_append, List.mem_map, Finset.mem_toList] at hq
    rcases hq with rfl | rfl | ⟨a, -, rfl⟩ | ⟨x, hx, rfl⟩
    · exact (GlobalTheory.MonBlock.monSupply.2 C V _ _ _ (X z) (F z) 0 _ _).1
    · exact (GlobalTheory.MonBlock.monSupply.2 C V _ _ _ (X z) (F z) 1 _ _).1
    · exact (GlobalTheory.T.characterBlocks_attain_bound.2 C V _ _ _ (X z) (F z) _ a (big_bg _ (alt z hz) a) _).1 (alt z hz)
    · rw [(hn z).1, (hn z).2]
      exact hatt z hz _ _ (Finset.mem_filter.1 hx).2
  · refine le_trans ?_ what₂
    have hc := card_reps P Z hZ
    rw [hP.card] at hc
    have hd : 1 ≤ P.d := Nat.pos_of_ne_zero (NeZero.ne _)
    calc _ ≤ ∑ z ∈ Z, (P.d * (i0 P.k V.l * (P.k - 1)) + 2 * P.r * P.d) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have := blocks_rows (X z) (p z) (ga z) P.r _ hi0 (hlev z hz)
          refine this.trans ?_
          rw [(hn z).1]
          exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hd) _
      _ = _ := by
          rw [Finset.sum_const, smul_eq_mul, ← hc]
          change _ = Z.card * P.d * (i0 P.k V.l * (P.k - 1)) + _
          ring
  · intro z hz g a k
    refine blocks_wt (X z) (alt z hz) (p z) (ga z) P.r ?_ (wt.supp z hz) ?_ g a k
    · have h1 := (hn z).1
      have h2 : (X z).j + (X z).j' = P.m := (hn z).2
      have := hP.r_eq
      omega
    · intro a
      rw [(hn z).1]
      exact wt.main z hz a

end GlobalTheory.PlanValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuationBlockPolynomialGeProdStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_blockPolynomial_ge_prod : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (Ty : Type) [Fintype Ty] [DecidableEq Ty] (r : Ty → ℕ) (n : ℕ) (β : (Σ τ : Ty, Fin (r τ)) → Fin n), Function.Injective β → ∀ (a : Ty → ℕ → ℕ), Crude.Dom r a → ∀ (yv : Letter Ty r n → O) (x : Ty → NNReal), (∀ τ, x τ ≤ 1) → (∀ τ (i : Fin (r τ)), x τ ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => yv ⟨τ, Fin.castLE i.isLt a, β ⟨τ, Fin.castLE i.isLt b⟩⟩).det)) → (∏ τ, x τ ^ (a τ 0) ≤ v (algebraMap O C (MvPolynomial.eval yv (Crude.crP r n O β a)))) ∧ ∀ mo ∈ (Crude.crP r n O β a).support, ∀ ℓ, mo ℓ ≠ 0 → ∃ i, β ⟨ℓ.1, i⟩ = ℓ.2.2 := by
  first | exact @GlobalTheory.CharDepth.valuation_blockPoly_ge | exact GlobalTheory.CharDepth.valuation_blockPoly_ge | (intros; apply GlobalTheory.CharDepth.valuation_blockPoly_ge <;> assumption)
end

