import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0104
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionAcrossHypersurfaceValuesAtZeros
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousOfDense
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0720
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTaylorAlgHomHolomorphicNilpotent
section
set_option autoImplicit false

open Filter Topology TopologicalSpace

namespace GlobalTheory.AnPer.TaylorHom

open GlobalTheory.AnPer GlobalTheory.PeriodFamily

variable {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R]

theorem fn_add_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (f g : Hol V) :
    (f + g).fn =ᶠ[𝓝 0] fun z ↦ f.fn z + g.fn z := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_add f g hq

theorem fn_mul_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (f g : Hol V) :
    (f * g).fn =ᶠ[𝓝 0] fun z ↦ f.fn z * g.fn z := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_mul f g hq

theorem fn_algebraMap_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (c : ℂ) :
    (algebraMap ℂ (Hol V) c).fn =ᶠ[𝓝 0] fun _ ↦ c := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_algebraMap c hq

theorem taylor_algebraMap (N : ℕ) (t : I → R) {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (c : ℂ) :
    GlobalTheory.PeriodFamily.taylor N t (algebraMap ℂ (Hol V) c).fn = algebraMap ℂ R c := by
  rw [taylor_congr_germ N t _ _ (fn_algebraMap_eventually h0 c), taylor_const_fun]

noncomputable def taylorHom (N : ℕ) (t : I → R) (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0)
    (V : Opens (I → ℂ)) (h0 : (0 : I → ℂ) ∈ V) : Hol V →ₐ[ℂ] R where
  toFun f := GlobalTheory.PeriodFamily.taylor N t f.fn
  map_one' := by
    have h : (1 : Hol V) = algebraMap ℂ (Hol V) 1 := (map_one _).symm
    change GlobalTheory.PeriodFamily.taylor N t (1 : Hol V).fn = 1
    rw [h, taylor_algebraMap N t h0, map_one]
  map_mul' f g := by
    change GlobalTheory.PeriodFamily.taylor N t (f * g).fn = GlobalTheory.PeriodFamily.taylor N t f.fn * GlobalTheory.PeriodFamily.taylor N t g.fn
    rw [taylor_congr_germ N t _ _ (fn_mul_eventually h0 f g)]
    exact taylor_mul_of_prod_eq_zero N t ht _ _ (f.analytic 0 h0) (g.analytic 0 h0)
  map_zero' := by
    have h : (0 : Hol V) = algebraMap ℂ (Hol V) 0 := (map_zero _).symm
    change GlobalTheory.PeriodFamily.taylor N t (0 : Hol V).fn = 0
    rw [h, taylor_algebraMap N t h0, map_zero]
  map_add' f g := by
    change GlobalTheory.PeriodFamily.taylor N t (f + g).fn = GlobalTheory.PeriodFamily.taylor N t f.fn + GlobalTheory.PeriodFamily.taylor N t g.fn
    rw [taylor_congr_germ N t _ _ (fn_add_eventually h0 f g)]
    exact taylor_add_of_analyticAt N t _ _ (f.analytic 0 h0) (g.analytic 0 h0)
  commutes' c := taylor_algebraMap N t h0 c

end GlobalTheory.AnPer.TaylorHom

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

theorem GlobalTheory.AnPer.exists_taylor_algHom : ∀ {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (V : Opens (I → ℂ)), 0 ∈ V → ∃ θ : Hol V →ₐ[ℂ] R, ∀ f, θ f = GlobalTheory.PeriodFamily.taylor N t f.fn := by
  intro I _ _ R _ _ N t ht V h0
  exact ⟨GlobalTheory.AnPer.TaylorHom.taylorHom N t ht V h0, fun f ↦ rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLiftOfAnalyticThickeningStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorLift_of_analyticThickening : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (S : K₀.DObj (et : Hol F₀.V →+* R) M), ∃ ψ : R ⊗[ℂ] Hol (K₀.W S.T.k) →+* S.T.C, ∀ (d : R) (h : Hol (K₀.W S.T.k)), ψ (d ⊗ₜ[ℂ] h) = algebraMap R S.T.C d * S.T.ρ h := by
  first | exact @GlobalTheory.AnPer.exists_tensorLift_of_DObj | exact GlobalTheory.AnPer.exists_tensorLift_of_DObj | (intros; apply GlobalTheory.AnPer.exists_tensorLift_of_DObj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHarishChandraDiscreteSeries
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section

namespace GlobalTheory.DiscreteSeriesUnitary

def unitaryModule {p q : ℕ} {T : GrpData p q} (D : DSRep T) : UGKMod p q where
  M := D.HK
  ip := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => inner ℂ (D.ι x) (D.ι y))
    (fun x y z => by simp only [map_add, inner_add_left])
    (fun c x y => by simp only [map_smul, inner_smul_left, smul_eq_mul])
    (fun x y z => by simp only [map_add, inner_add_right])
    (fun c x y => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
  herm x y := inner_conj_symm (D.ι y) (D.ι x)
  pos x hx := by
    have h : D.ι x ≠ 0 := fun h => hx (D.ι_inj (h.trans (map_zero D.ι).symm))
    exact re_inner_self_pos (𝕜 := ℂ).2 h
  adj Z x y := GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint p q T D.U D.HK D.ι D.der Z x y

theorem exists_unitary : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T),
    ∃ M : UGKMod p q, M.M = D.HK :=
  fun _ _ _ D => ⟨unitaryModule D, rfl⟩

end GlobalTheory.DiscreteSeriesUnitary

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitsComparingLiftedTransitionsFactor
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftUnits

theorem le_pre_inf {X Y : Scheme.{0}} {y : Y ⟶ X} {U V : X.Opens} (hU : ⊤ ≤ y ⁻¹ᵁ U) (hV : ⊤ ≤ y ⁻¹ᵁ V) :
    ⊤ ≤ y ⁻¹ᵁ (U ⊓ V) := fun _ hp => ⟨hU hp, hV hp⟩

theorem le_pre_of_eq {X Y Z : Scheme.{0}} {f : Z ⟶ Y} {y : Y ⟶ X} {z : Z ⟶ X} (e : f ≫ y = z) {U : X.Opens}
    (hU : ⊤ ≤ y ⁻¹ᵁ U) : ⊤ ≤ z ⁻¹ᵁ U := by
  subst e
  intro p _
  exact hU (Set.mem_univ (f p))

theorem map_evalAt {X : Scheme.{0}} {C C' : Type} [CommRing C] [CommRing C'] (φ : C →+* C') {x : Sp C ⟶ X}
    {y : Sp C' ⟶ X} (e : spMap φ ≫ x = y) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)) :
    φ (evalAt x U h f) = evalAt y U h' f := by
  subst e
  obtain ⟨_, hn, -⟩ := GlobalTheory.EvalNat.evalAt_natural φ x U h
  exact (hn f).symm

theorem evalAt_g_mul {X : Scheme.{0}} {C : Type} [CommRing C] {M : LB X} (hM : M.IsLB) (y : Sp C ⟶ X) {a b c : M.ι}
    (ha : ⊤ ≤ y ⁻¹ᵁ M.U a) (hb : ⊤ ≤ y ⁻¹ᵁ M.U b) (hc : ⊤ ≤ y ⁻¹ᵁ M.U c) :
    evalAt y _ (le_pre_inf ha hb) (M.g a b).val * evalAt y _ (le_pre_inf hb hc) (M.g b c).val =
      evalAt y _ (le_pre_inf ha hc) (M.g a c).val := by
  have hres : ∀ {U V : X.Opens} (h : V ≤ U) (u : (Γ(X, U))ˣ),
      ((res h u : (Γ(X, V))ˣ) : Γ(X, V)) = (X.presheaf.map (homOfLE h).op).hom (u : Γ(X, U)) := fun _ _ => rfl
  have q2 := congrArg (fun u => evalAt y (M.U a ⊓ M.U b ⊓ M.U c) (le_pre_inf (le_pre_inf ha hb) hc) (Units.val u))
    (hM.cocycle a b c)
  simp only [Units.val_mul, map_mul, hres] at q2
  obtain ⟨_, -, hr⟩ := GlobalTheory.EvalNat.evalAt_natural (RingHom.id C) y (M.U a ⊓ M.U b ⊓ M.U c) (le_pre_inf (le_pre_inf ha hb) hc)
  rw [hr (M.U a ⊓ M.U b) (le_trans inf_le_left le_rfl) (le_pre_inf ha hb),
    hr (M.U b ⊓ M.U c) (le_inf (le_trans inf_le_left inf_le_right) inf_le_right) (le_pre_inf hb hc),
    hr (M.U a ⊓ M.U c) (le_inf (le_trans inf_le_left inf_le_left) inf_le_right) (le_pre_inf ha hc)]
  exact q2

theorem isUnit_evalAt {X : Scheme.{0}} {C : Type} [CommRing C] (y : Sp C ⟶ X) {U : X.Opens} (h : ⊤ ≤ y ⁻¹ᵁ U)
    (u : Γ(X, U)ˣ) : IsUnit (evalAt y U h u.val) := u.isUnit.map (evalAt y U h)

theorem mul_eq_one_of_covolume_identity {R : Type} [CommRing R] {g₁ g₂ g₃ g₄ g₅ u v w A S f : R} (c₁ : g₁ * g₂ = g₅) (c₂ : g₃ * g₄ = g₅)
    (hu : u = g₁) (hv : v = g₂ * S) (hw : w = g₃ * f) (hf : f = g₄ * A * S) : u * v * A = w := by
  subst hu hv hw hf
  linear_combination (S * A) * c₁ - (S * A) * c₂

theorem exists_units : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X), M.IsLB → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ (fr : ∀ k, Hol (K.W k)) (a : Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) → (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) → ∀ (i : K.Obj → M.ι), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) → ∀ (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C), (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) → ∃ e : ∀ T : K.Obj, (T.C)ˣ, (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) := by
  intro I _ g Λ _ F B _ X s σ K r M hM j hj fr a hfr hcoc i hi uu huu
  have hjT : ∀ T : K.Obj, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (j T.k) := fun T =>
    le_pre_of_eq (f := spMap ((Ideal.Quotient.mk T.J).comp T.ρ)) (y := r.x T.k) rfl (hj T.k)
  have hlift : ∀ T : K.Obj, ∃ c : T.C, IsUnit c ∧ Ideal.Quotient.mk T.J c =
      @id (T.C ⧸ T.J) (evalAt (r.obj T).x _ (le_pre_inf (hi T) (hjT T)) (M.g (i T) (j T.k)).val) *
        Ideal.Quotient.mk T.J (T.ρ (fr T.k)) := by
    intro T
    have hu : IsUnit (@id (T.C ⧸ T.J) (evalAt (r.obj T).x _ (le_pre_inf (hi T) (hjT T)) (M.g (i T) (j T.k)).val) *
        Ideal.Quotient.mk T.J (T.ρ (fr T.k))) :=
      (isUnit_evalAt (r.obj T).x (le_pre_inf (hi T) (hjT T)) (M.g (i T) (j T.k))).mul
        (((hfr T.k).map T.ρ).map (Ideal.Quotient.mk T.J))
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (@id (T.C ⧸ T.J) (evalAt (r.obj T).x _ (le_pre_inf (hi T) (hjT T))
      (M.g (i T) (j T.k)).val) * Ideal.Quotient.mk T.J (T.ρ (fr T.k)))
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (((hu.unit⁻¹ : (T.C ⧸ T.J)ˣ)) : T.C ⧸ T.J)
    refine ⟨c, ?_, hc⟩
    have hmem : c * d - 1 ∈ T.J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, hd, map_one, IsUnit.mul_val_inv, sub_self]
    have hnil : IsNilpotent (c * d - 1) := by
      obtain ⟨n, hn⟩ := T.nil
      refine ⟨n, ?_⟩
      have hp := Ideal.pow_mem_pow hmem n
      rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hp
    have hcd : IsUnit (c * d) := by
      have h1 := hnil.isUnit_one_add
      rwa [add_sub_cancel] at h1
    exact isUnit_of_mul_isUnit_left hcd
  choose c hcu hcε using hlift
  refine ⟨fun T => (hcu T).unit, ?_⟩
  intro T T' φ
  have hle : K.le φ.deg T'.k T.k := Charts.Hom.le φ
  have hiT : ⊤ ≤ (r.obj T').x ⁻¹ᵁ M.U (i T) :=
    le_pre_of_eq (f := spMap (Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem)) (y := (r.obj T).x) (r.analyticChartsRealization_comp_point_eq φ) (hi T)
  have hjk : ⊤ ≤ (r.obj T').x ⁻¹ᵁ M.U (j T.k) :=
    le_pre_of_eq (f := spMap (Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem)) (y := (r.obj T).x) (r.analyticChartsRealization_comp_point_eq φ) (hjT T)
  have hxk : ⊤ ≤ r.x T'.k ⁻¹ᵁ (M.U (j T'.k) ⊓ M.U (j T.k)) :=
    le_pre_inf (hj T'.k) (le_pre_of_eq (r.compat hle) (hj T.k))
  have c₁ := evalAt_g_mul hM (r.obj T').x (hi T') hiT hjk
  have c₂ := evalAt_g_mul hM (r.obj T').x (hi T') (hjT T') hjk
  have hu := huu T T' φ (le_pre_inf (hi T') hiT)
  have hS : Ideal.Quotient.mk T'.J (φ.φ (T.ρ (fr T.k))) =
      Ideal.Quotient.mk T'.J (T'.ρ (Charts.sh hle (fr T.k))) :=
    Ideal.Quotient.eq.mpr (Close.sub_mem φ.close (fr T.k))
  have hv : Ideal.Quotient.mk T'.J (φ.φ (c T)) =
      @id (T'.C ⧸ T'.J) (evalAt (r.obj T').x _ (le_pre_inf hiT hjk) (M.g (i T) (j T.k)).val) *
        Ideal.Quotient.mk T'.J (T'.ρ (Charts.sh hle (fr T.k))) := by
    have h1 : Ideal.Quotient.mk T'.J (φ.φ (c T)) =
        Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem (Ideal.Quotient.mk T.J (c T)) := by
      rfl
    have h2 : Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem (Ideal.Quotient.mk T.J (T.ρ (fr T.k))) =
        Ideal.Quotient.mk T'.J (φ.φ (T.ρ (fr T.k))) := by
      rfl
    rw [h1, hcε T, map_mul, h2, hS]
    congr 1
    exact map_evalAt (Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem) (x := (r.obj T).x) (y := (r.obj T').x)
      (r.analyticChartsRealization_comp_point_eq φ) _ (le_pre_inf hiT hjk) _
  have hf : Ideal.Quotient.mk T'.J (T'.ρ (fr T'.k)) =
      @id (T'.C ⧸ T'.J) (evalAt (r.obj T').x _ (le_pre_inf (hjT T') hjk) (M.g (j T'.k) (j T.k)).val) *
        Ideal.Quotient.mk T'.J (T'.ρ (a φ.deg T'.k)) * Ideal.Quotient.mk T'.J (T'.ρ (Charts.sh hle (fr T.k))) := by
    rw [hcoc φ.deg T'.k T.k hle hxk, map_mul, map_mul, map_mul, map_mul]
    congr 2
    exact map_evalAt ((Ideal.Quotient.mk T'.J).comp T'.ρ) (x := r.x T'.k) (y := (r.obj T').x) rfl _ _ _
  refine Ideal.Quotient.eq.mp ?_
  rw [map_mul, map_mul]
  exact mul_eq_one_of_covolume_identity (R := T'.C ⧸ T'.J) c₁ c₂ hu hv (hcε T') hf

end GlobalTheory.LiftUnits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionAcrossHypersurfaceValuesAtZerosStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_across_hypersurface_values_at_zeros : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, jacAt A s P ≠ 0) → (∀ y, A.sqn L s y ≤ 1) → ∀ δ : ℝ, 0 < δ → ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → ∀ (Ω : Set Y) (h : ι → Y → ℂ) (T : ℝ) (θ : ℝ → ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) → A.zeroSet s ⊆ Ω → IsCut T θ → ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu < ⊤ → ∀ F : ι → Y → ℂ, A.IsSecOn (A.kap + E) (nz A τ) F → ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu < ⊤ → ∃ G : ι → Y → ℂ, A.IsSec (A.kap + E) G ∧ (∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source → G i y = F i y) ∧ ∀ P ∈ A.zeroSet s, G (A.pick P) P = h (A.pick P) P := by
  first | exact @GlobalTheory.OTY.extension_values_at_zeros | exact GlobalTheory.OTY.extension_values_at_zeros | (intros; apply GlobalTheory.OTY.extension_values_at_zeros <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilIsSubDPIdeal
section
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem fil_isSubDPIdeal : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (N : ℕ), 1 ≤ N →
    δ.IsSubDPIdeal (fil δ N) := by
  intro B _ J δ N hN
  refine ⟨GlobalTheory.Cris.ExpBij.dpFil_le δ hN, fun n hn j hj ↦ ?_⟩
  have h := GlobalTheory.Cris.ExpBij.dpow_mem_dpFil_mul δ hN hj n
  exact GlobalTheory.Cris.ExpBij.dpFil_anti δ (Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero hn)) h

end GlobalTheory.PDA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilProperties
section
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem map_fil_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {C : Type} [CommRing C]
    {J' : Ideal C} (δ' : DividedPowers J') (f : B →+* C) (hf : IsDPMorphism δ δ' f) (N : ℕ) :
    (fil δ N).map f ≤ fil δ' N := by
  rw [Ideal.map_le_iff_le_comap, fil, Ideal.span_le]
  rintro _ ⟨l, h1, h2, rfl⟩
  have hJ : ∀ p ∈ l, f p.2 ∈ J' := fun p hp ↦ hf.ideal_comp (Ideal.mem_map_of_mem f (h1 p hp))
  refine Ideal.subset_span ⟨l.map fun p ↦ (p.1, f p.2), ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact hJ p hp
  · simpa [List.map_map, Function.comp_def] using h2
  · rw [map_list_prod, List.map_map, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun p hp ↦ ?_)
    simp only [Function.comp_apply]
    exact (hf.dpow_comp (n := p.1) p.2 (h1 p hp)).symm

theorem fil_properties : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J), fil δ 0 = ⊤ ∧ fil δ 1 = J ∧ (∀ m n, m ≤ n → fil δ n ≤ fil δ m) ∧ (∀ m n, fil δ m * fil δ n ≤ fil δ (m + n)) ∧ (∀ n, ∀ x ∈ J, δ.dpow n x ∈ fil δ n) ∧ (IsNilDP δ ↔ ∃ N, IsLev δ N) ∧ ∀ (C : Type) [CommRing C] (J' : Ideal C) (δ' : DividedPowers J') (f : B →+* C), IsDPMorphism δ δ' f → ∀ N, (fil δ N).map f ≤ fil δ' N := by
  intro B _ J δ
  refine ⟨fil_zero_eq_top δ, fil_one_eq δ, fun m n h ↦ GlobalTheory.Cris.ExpBij.dpFil_anti δ h, fun m n ↦ ?_,
    fun n x hx ↦ GlobalTheory.Cris.ExpBij.dpow_mem_dpFil δ hx n, isDPNilpotent_iff_exists_isLevel δ,
    fun C _ J' δ' f hf N ↦ map_fil_le δ δ' f hf N⟩
  rw [Ideal.mul_le]
  exact fun a ha b hb ↦ GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ ha hb

end GlobalTheory.PDA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveOfLocalBasis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieProj

theorem finite_projective_of_localBasis : ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ),
    (∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal,
      Nonempty (Module.Basis (Fin n) (Localization.Away r) (LocalizedModule (Submonoid.powers r) M))) →
    Module.Finite R M ∧ Module.Projective R M ∧ ∀ p, Module.rankAtStalk (R := R) M p = n := by
  intro R M _ _ _ n h
  let t : Set R := {r | Nonempty (Module.Basis (Fin n) (Localization.Away r)
    (LocalizedModule (Submonoid.powers r) M))}
  have ht : Ideal.span t = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hb⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hle (Ideal.subset_span hb))
  have hfree : ∀ g : t, Module.Free (Localization.Away g.1) (LocalizedModule (Submonoid.powers g.1) M) :=
    fun g => Module.Free.of_basis g.2.some
  have hfp : ∀ g : t, Module.FinitePresentation (Localization.Away g.1)
      (LocalizedModule (Submonoid.powers g.1) M) := fun g => by
    haveI := hfree g
    haveI : Module.Finite (Localization.Away g.1) (LocalizedModule (Submonoid.powers g.1) M) :=
      Module.Finite.of_basis g.2.some
    exact Module.finitePresentation_of_projective _ _
  haveI : Module.FinitePresentation R M := Module.FinitePresentation.of_localizationSpan t ht hfp
  haveI : Module.Flat R M := by
    refine Module.flat_of_localized_span R M t ht ?_
    intro g
    haveI := hfree g
    haveI : Module.Flat R (Localization.Away g.1) := IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) _
  refine ⟨inferInstance, Module.Flat.projective_of_finitePresentation, fun p => ?_⟩
  obtain ⟨r, hr, ⟨b⟩⟩ := h p
  have hq : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨q, rfl⟩ := hq
  haveI := Module.Free.of_basis b
  haveI : Nontrivial (Localization.Away r) := q.nontrivial
  rw [← Module.rankAtStalk_isBaseChange
    (LocalizedModule.isBaseChange (Submonoid.powers r) M) q,
    Module.rankAtStalk_eq_finrank_of_free]
  change Module.finrank (Localization.Away r) (LocalizedModule (Submonoid.powers r) M) = n
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

theorem exists_chart_lieBasis : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ),
    SmoothOfRelativeDimension n G.hom → ∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal,
      Nonempty (ReciprocityTheory.ChartRestriction.G.Chart.Chart (ReciprocityTheory.ChartRestriction.G.Chart.Gs G r)) ∧
      ∃ v : Fin n → (epsR (Localization.Away r) ⟶ ReciprocityTheory.ChartRestriction.G.Chart.Gs G r), IsLieBasis v := by
  intro R _ G _ _ n h p
  let e : Spec (CommRingCat.of R) ⟶ G.left := η[G].left
  obtain ⟨S, _, _, j, hS, hj, hmem⟩ := GlobalTheory.LieLoc.exists_standardSmooth_chart G n h (e p)
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := (e ⁻¹ᵁ j.left.opensRange).1) hmem (e ⁻¹ᵁ j.left.opensRange).2
  refine ⟨r, hr, ReciprocityTheory.ChartRestriction.G.Chart.chart_away G j.left.opensRange (by haveI : IsAffine (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) S).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of S))); exact isAffineOpen_opensRange j.left) r
    (fun x hx => hsub (show x ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) from hx)), ?_⟩
  obtain ⟨ε, hε⟩ := GlobalTheory.SqZero.exists_chart_pt j
    (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (Localization.Away r) ⟶ G) (by
    rintro _ ⟨t, rfl⟩
    have : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) t ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨t, rfl⟩
    exact hsub this)
  obtain ⟨x, hx⟩ := GlobalTheory.LieLoc.univChart_baseChange G n S j _ ε hε.symm
  exact ⟨_, ReciprocityTheory.ChartRestriction.G.Chart.basis_of_chart hx⟩

end GlobalTheory.LieProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShape
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.JointHarm

theorem finrank_joint_highest_of_shape :
    ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), JointShape p q r s μ μ' →
      Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (jointHarm p q r s)) = 1 :=
  fun _ _ _ _ μ μ' => (joint_harmonics μ μ').1

end GlobalTheory.JointHarm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAdjointOrthogonalInjective
section
noncomputable section
namespace GlobalTheory.FockAdj
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem inner_monomial_left (hι : IsFockIP ι) (α : σ →₀ ℕ) (Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (monomial α 1)) (ι Q) =
      coeff α Q * α.prod (fun _ k => (k.factorial : ℂ)) := by
  induction Q using MvPolynomial.induction_on' with
  | add Q Q' h h' => simp only [map_add, inner_add_right, h, h', coeff_add, add_mul]
  | monomial β b =>
    have hm : (monomial β b : MvPolynomial σ ℂ) = b • monomial β 1 := by
      rw [smul_monomial]; simp
    rw [coeff_monomial]
    conv_lhs => rw [hm]
    rw [map_smul, inner_smul_right, hι]
    by_cases h : α = β
    · subst h; simp
    · simp [h, Ne.symm h]

theorem inner_eq_zero_of_isHomogeneous (hι : IsFockIP ι) {d e : ℕ} {P Q : MvPolynomial σ ℂ}
    (hde : d ≠ e) (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous e) :
    inner ℂ (ι P) (ι Q) = 0 := by
  rw [P.as_sum, map_sum, sum_inner]
  refine Finset.sum_eq_zero fun α hα => ?_
  have hm : (monomial α (coeff α P) : MvPolynomial σ ℂ) = coeff α P • monomial α 1 := by
    rw [smul_monomial]; simp
  have h0 : coeff α Q = 0 := by
    by_contra hc
    exact hde ((hP (mem_support_iff.mp hα)).symm.trans (hQ hc))
  rw [hm, map_smul, inner_smul_left, inner_monomial_left hι, h0, zero_mul, mul_zero]

theorem injective_of_isFockIP (hι : IsFockIP ι) : Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  ext α
  have h := inner_monomial_left hι α P
  rw [hP, inner_zero_right] at h
  have hne : α.prod (fun _ k => (k.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simpa [hne] using h.symm

theorem fock_adjoint_orthogonal_injective :
    ∀ (σ : Type) [DecidableEq σ] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (ι : MvPolynomial σ ℂ →ₗ[ℂ] H), IsFockIP ι →
      (∀ (i : σ) (P Q : MvPolynomial σ ℂ),
        inner ℂ (ι (X i * P)) (ι Q) = inner ℂ (ι P) (ι (pderiv i Q))) ∧
      (∀ (d e : ℕ) (P Q : MvPolynomial σ ℂ), d ≠ e → P ∈ homog σ d → Q ∈ homog σ e →
        inner ℂ (ι P) (ι Q) = 0) ∧ Function.Injective ι :=
  fun _ _ _ _ _ _ hι => ⟨GlobalTheory.FockDeg.inner_X_mul hι,
    fun _ _ _ _ hde hP hQ => inner_eq_zero_of_isHomogeneous hι hde hP hQ,
    injective_of_isFockIP hι⟩

end GlobalTheory.FockAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg

open GlobalTheory.JointHarm GlobalTheory.FockSeq in

theorem harmonic_homog_of_type : ∀ (p q r s : ℕ),
    (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
      P ∈ harm1 p q r s →
      ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
    (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
      P ∈ harm2 p q r s →
      ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d) :=
  fun _ _ _ _ =>
    ⟨fun _ P h0 ht hh => isSide_one.homog_of_type isFockIsometry_embedding emb_injective
        Function.bijective_id h0 ht ((mem_harm1 P).1 hh),
      fun _ P h0 ht hh => isSide_two.homog_of_type isFockIsometry_embedding emb_injective
        Prod.swap_bijective h0 ht ((mem_harm2 P).1 hh)⟩

end GlobalTheory.FockAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquarePropertiesStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_evalSquare_properties : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n f, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 ∧ c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f ∧ c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) ∧ c.ev₂ n (cob1 c.μ f) = cobOne O (G.A n) (c.ev n f) := by
  first | exact @GlobalTheory.QLog.Chart.ev₂_eval | exact GlobalTheory.QLog.Chart.ev₂_eval | (intros; apply GlobalTheory.QLog.Chart.ev₂_eval <;> assumption)
end

