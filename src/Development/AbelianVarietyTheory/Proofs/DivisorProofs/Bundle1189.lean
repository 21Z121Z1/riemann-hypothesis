import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFPreservesIsThetaFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreePullBirationalModel
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem isometric_pull_shiftC {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    (L : HermLB p) (t : ℝ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.shift (fun _ => t) fun _ => rfl).pull π hπ).Isometric ((L.pull π hπ).shift (fun _ => t) fun _ => rfl) :=
  HermLB.isometric_of_eqOn fun σ a y _ => by
    exact (congrArg (· + 2 * t) (Weight.pull_φ (L.φ σ) π hπ a y)).trans
      (Weight.pull_φ ((L.φ σ).addFn fun _ => 2 * t) π hπ a y).symm

theorem gdeg_pull_model : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q)
    (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ L : HermLB p, gdeg (L.pull π hπ) D = gdeg L D ∧
    ∀ (a t : ℝ), L.IsSelfInter a →
      ((L.pull π hπ).shift (fun _ => t) fun _ => rfl).IsSelfInter (a + ((D : ℝ) + 1) * t * gdeg L D) := by
  intro hC k _ X Y _ _ p q D hX hY π hπ φ hM L
  have hdeg : π.residueDegree (genericPoint Y) ≠ 0 := by rw [hM.deg]; exact one_ne_zero
  have hP := ((hC.arProj k X Y p q D hX hY π hπ hM.gen hdeg).1)
  have hP1 : ∀ (M : HermLB p) (a : ℝ), M.IsSelfInter a → (M.pull π hπ).IsSelfInter a := fun M a h => by
    have := hP M a h
    rwa [hM.deg, Nat.cast_one, one_mul] at this
  have hS := hC.arShift
  have hg : gdeg (L.pull π hπ) D = gdeg L D := by
    obtain ⟨h, hh⟩ := ((hC.arExists k X p D hX).1 L)
    have ha : L.IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
    set a := h (genericPoint X)

    have h1 := hP1 _ _ (hS k X p D hX L a 1 ha)
    have h1' := (isometric_pull_shiftC L 1 π hπ).isSelfInter hY h1
    have h2 := hS k Y q D hY (L.pull π hπ) a 1 (hP1 L a ha)
    have e := HermLB.IsSelfInter.unique hY h1' h2
    have hD : ((D : ℝ) + 1) ≠ 0 := by positivity
    have : ((D : ℝ) + 1) * gdeg L D = ((D : ℝ) + 1) * gdeg (L.pull π hπ) D := by linarith
    exact (mul_left_cancel₀ hD this).symm
  refine ⟨hg, fun a t ha => ?_⟩
  have := hS k Y q D hY (L.pull π hπ) a t (hP1 L a ha)
  rwa [hg] at this

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodScalarOfIsAdelicScalar
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftScalarCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Source

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem span_jVx (hV : R.models_HV) (hj : R.models_jV) : Submodule.span ℂ (Set.range (jVx R i A.μ0)) = ⊤ := by
  have h0 : (R.HV i A.μ0).e '' Set.range (jVx R i A.μ0) = Set.range (R.B.jL i A.μ0) :=
    (Set.range_comp _ _).symm.trans (congrArg Set.range (funext (hj i A.μ0)))
  have h1 : (Submodule.span ℂ (Set.range (jVx R i A.μ0))).map (R.HV i A.μ0).e = (⊤ : Submodule ℂ _).map (R.HV i A.μ0).e :=
    ((Submodule.map_span _ _).trans (congrArg (Submodule.span ℂ) h0)).trans
      ((GlobalTheory.PresBasic.ext_span (R.B.L i A.μ0).pres).trans ((hV i A.μ0).2.1.symm.trans (LinearMap.range_eq_map _)))
  exact Submodule.map_injective_of_injective (hV i A.μ0).1 h1

end Source

section Target

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem eval_inj (hW : R.models_HW) {v₀ : (R.MW i (sg0 D A)).Vec} (hv : IsChosenExtremalVector R i (sg0 D A) v₀) {x y : (R.HW i (sg0 D A)).H}
    (h : (R.HW i (sg0 D A)).e x v₀ = (R.HW i (sg0 D A)).e y v₀) : x = y := by
  have h0 : (R.HW i (sg0 D A)).e (x - y) v₀ = 0 := by
    rw [LinearMap.map_sub]
    exact sub_eq_zero.2 h
  have h1 := (hW i (sg0 D A)).2.2 (x - y) (x - y)
  rw [ipAt, GlobalTheory.EvalAtUnitVector.ipM_self_eq_zero _ _ _ _ v₀ (IsChosenExtremalVector.norm R hv) h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

theorem eC_idem (hr : R.grp_record) : GoodBasisCentralIdempotents.IsCentralIdem (RealDat.eC (A := A) (sg0 D A)) := by
  obtain ⟨eR, _, _, h, _⟩ := hr
  have h0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have h1 : ∀ g, RealDat.eC (A := A) (sg0 D A) g = D.ntypes.e0.coeff (eR g) := fun g => by rw [h0]; exact h g
  obtain ⟨h2, h3⟩ := GlobalTheory.GoodLatCompare.isCentralIdempotent_of_goodSeriesIdempotent (D := D) (RingHom.id ℂ) (eC := fun g => D.ntypes.e0.coeff g) fun _ => rfl
  refine ⟨fun g k => ?_, fun g => ?_⟩
  · rw [h1, h1, map_mul eR, map_mul eR, map_inv eR]
    exact h2 _ _
  · rw [h1]
    refine Eq.trans (Fintype.sum_equiv eR.toEquiv _ _ fun k => ?_) (h3 (eR g))
    rw [h1, h1, map_mul eR, map_inv eR]
    rfl

def projW (R : RealDat D A Ks) (i : Fin D.R.m) : (R.HW i (sg0 D A)).H →ₗ[ℂ] (R.HW i (sg0 D A)).H :=
  ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g

theorem postOn_of_good {P : LevelP R.Pg D.R.r ℂ} {U : MMap (R.MW i (sg0 D A))} (hU : U ∈ R.Wat i (sg0 D A) P) :
    postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) U = U :=
  sub_eq_zero.1 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hU).2)

def GoodScalar (R : RealDat D A Ks) (i : Fin D.R.m) (c : HookProductDictionary.EigSys D) (l : ℝ) : Prop :=
  ∀ U ∈ R.Wat i (sg0 D A) R.triv ⊓ AdelicScalarSectionLift.cuspPart R i c, ∃ y : (R.HV i A.μ0).H,
    (∀ f, ipAt (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) U (R.thF i A.μ0 f) = ⟪y, f⟫_ℂ) ∧
      postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) (R.thF i A.μ0 y) = (l : ℂ) • U

end Target

section Geometric

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

def tr : AdelicScalarSectionLift.Sec O →ₗ[ℂ] AdelicScalarSectionLift.Sec O := GlobalTheory.CuspSecCompare.trunc (C.U ((i : ℕ) + 1) O.s0).X

structure DictFacts : Prop where
  dom : ∀ g, (O.dict g).2 ∈ ((C.U ((i : ℕ) + 1) O.s0).X (O.dict g).1).dom
  mu : ∀ g, ‖O.mu g‖ = 1
  cc : ∀ k, ‖cc k‖ = 1
  lifts : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv)

def prin : Submodule ℂ (AdelicScalarSectionLift.Sec O) where
  carrier := {S | Lev.HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (AdelicScalarSectionLift.dict O κ cc S)}
  zero_mem' := fun k _ h => by
    rw [LinearMap.map_zero]
    exact (mul_zero _).symm
  add_mem' := fun {S S'} hS hS' k hk h => by
    rw [LinearMap.map_add]
    exact (congrArg₂ (· + ·) (hS k hk h) (hS' k hk h)).trans (mul_add _ _ _).symm
  smul_mem' := fun a S hS k hk h => by
    rw [LinearMap.map_smul]
    exact (congrArg (a * ·) (hS k hk h)).trans (mul_left_comm _ _ _)

def IntOn (S S' : AdelicScalarSectionLift.Sec O) : Prop :=
  IntegrableOn (fun g => AdelicScalarSectionLift.unitVal O κ S g * star (AdelicScalarSectionLift.unitVal O κ S' g)) (R.fdW i) (R.νW i)

variable {O cc} (hd : DictFacts O cc)
include hd

omit hd

variable (O cc)

def DictOnM (v₀ : (R.MW i (sg0 D A)).Vec) (P : LevelP R.Pg D.R.r ℂ) : Prop :=
  (∀ S ∈ AdelicScalarSectionLift.goodAt O κ cc P ⊓ prin O κ cc, AdelicScalarSectionLift.dict O κ cc S = 0 → S = 0) ∧
  (∀ S ∈ AdelicScalarSectionLift.goodAt O κ cc P ⊓ prin O κ cc, ∃ U ∈ R.Wat i (sg0 D A) P, U v₀ = AdelicScalarSectionLift.dict O κ cc S) ∧
  ∀ S ∈ AdelicScalarSectionLift.goodAt O κ cc P ⊓ prin O κ cc, ∀ S' ∈ AdelicScalarSectionLift.goodAt O κ cc P ⊓ prin O κ cc,
    ∀ U ∈ R.Wall i (sg0 D A), ∀ U' ∈ R.Wall i (sg0 D A), U v₀ = AdelicScalarSectionLift.dict O κ cc S → U' v₀ = AdelicScalarSectionLift.dict O κ cc S' →
      IntOn O κ S S' ∧ AdelicScalarSectionLift.ipSec O κ P S S' = ((Nat.card P.H : ℕ) : ℂ)⁻¹ * ipAt (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) U' U

def ActsOn (L : (R.HV i A.μ0).H →ₗ[ℂ] AdelicScalarSectionLift.Sec O) (P : LevelP R.Pg D.R.r ℂ) (c : HookProductDictionary.EigSys D) (l : ℝ) : Prop :=
  ∀ S ∈ AdelicScalarSectionLift.partAt O κ cc P c ⊓ prin O κ cc, ∃ y ∈ AdelicScalarSectionLift.srcAt R i P,
    (∀ f ∈ AdelicScalarSectionLift.srcAt R i P, IntOn O κ (L f) S ∧ AdelicScalarSectionLift.ipSec O κ P (L f) S = AdelicScalarSectionLift.ipSrc R i P f y) ∧ L y = (l : ℂ) • S

variable {O cc}

include hd

omit hd

end Geometric

section Main

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

abbrev Bound (i : Fin D.R.m) (b l : ℝ) : Prop :=
  AdelicScalarSectionLift.hookSum D i - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * AdelicScalarSectionLift.logSize D b ≤ Real.log l

def CommonPart (i : Fin D.R.m) : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → HookProductDictionary.RegularGaps D →
  ∀ (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph : ℂ), (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph →
    ∀ h, AdelicScalarSectionLift.IsRepSystem (O i) (v₀ i (sg0 D A)) h →
      (∃ th, AdelicScalarSectionLift.IsSecLift (O i) (κ i) h th) ∧ (∃ e, AdelicScalarSectionLift.IsSrcProj R i e) ∧
      ∀ s, DictOnM (O i) (κ i) cc (v₀ i (sg0 D A)) (AdelicScalarSectionLift.level R F s) ∧
        ∀ c, AdelicScalarSectionLift.partAt (O i) (κ i) cc (AdelicScalarSectionLift.level R F s) c ⊓ prin (O i) (κ i) cc ≠ ⊥ →
          ∃ l : ℝ, 0 < l ∧ (R.Wat i (sg0 D A) R.triv ⊓ AdelicScalarSectionLift.cuspPart R i c ≠ ⊥ ∧ GoodScalar R i c l) ∧
            (∀ th e, AdelicScalarSectionLift.IsSecLift (O i) (κ i) h th → AdelicScalarSectionLift.IsSrcProj R i e →
              ActsOn (O i) (κ i) cc (th ∘ₗ e) (AdelicScalarSectionLift.level R F s) c l) ∧
            ∀ b, (∀ j, AdelicScalarSectionLift.IsSize D j b) → Bound i b l

def ExtraClauses : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i →
  ∀ (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph : ℂ), (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph →
    AdelicScalarSectionLift.DictClauses (O i) (κ i) cc F (v₀ i (sg0 D A)) ∧
    ∀ h, AdelicScalarSectionLift.IsRepSystem (O i) (v₀ i (sg0 D A)) h →
      (∀ th th', AdelicScalarSectionLift.IsSecLift (O i) (κ i) h th → AdelicScalarSectionLift.IsSecLift (O i) (κ i) h th' → th = th') ∧
      ∀ b, AdelicScalarSectionLift.IsSize D i b → ∀ th, AdelicScalarSectionLift.IsSecLift (O i) (κ i) h th →
        (∀ y, th y ∈ AdelicScalarSectionLift.cuspC (O i) (κ i)) ∧
        (∃ (u : ℂ) (z : G), ‖u‖ = 1 ∧ z ∈ Subgroup.center G ∧ ∀ y,
          actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) (AdelicScalarSectionLift.dict (O i) (κ i) cc (th y)) =
            u • R.thF i A.μ0 y (v₀ i (sg0 D A))) ∧
        ∀ s c, AdelicScalarSectionLift.partAt (O i) (κ i) cc (AdelicScalarSectionLift.level R F s) c ≠ ⊥ → ∀ l, GoodScalar R i c l →
          AdelicScalarSectionLift.IsAdelicScalar R i c l ∧ ((¬ ∀ j, AdelicScalarSectionLift.IsSize D j b) → Bound i b l)

variable {T R F κ v₀ O}

variable (T R F κ v₀ O)

end Main

end GlobalTheory.LiftScalarCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphJetsMemPowSupUniformiser
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

theorem ker_productMap_le_span {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ']
    (ρ : κ →ₐ[ℂ] κ') :
    RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) ≤
      Ideal.span {x | ∃ f : κ, x = f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f} := by
  have key : ∀ x : κ ⊗[ℂ] κ',
      x - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x ∈
        Ideal.span {x | ∃ f : κ, x = f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f} := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      have e : f ⊗ₜ[ℂ] g - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') (f ⊗ₜ g) =
          (f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f) * (1 ⊗ₜ g) := by
        simp [Algebra.TensorProduct.productMap_apply_tmul, sub_mul,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨f, rfl⟩)
    | add x y hx hy =>
      have e : x + y - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') (x + y) =
          (x - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x) +
            (y - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') y) := by
        rw [map_add, TensorProduct.tmul_add]
        abel
      rw [e]
      exact add_mem hx hy
  intro x hx
  have h := key x
  rwa [RingHom.mem_ker.1 hx, TensorProduct.tmul_zero, sub_zero] at h

set_option maxHeartbeats 1000000 in

theorem jets_mem_pow_sup : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  graphIdeal E R π ρ ≤ 𝔭 → Irreducible t →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i →
    ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
    w ∈ 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} := by

  intro K κ κ' _ _ _ _ _ _ R π ρ E 𝔭 _ t hle ht hπC hC hfrac hR hord M l a b w hw hx
  let T := tens (κ' := κ') (placeAlg E)
  let I : Ideal T := 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩}
  let q : T →ₐ[ℂ] T ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hq0 : ∀ y : T, q y = 0 ↔ y ∈ I := fun y => by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  let jL : placeAlg E →ₐ[ℂ] T :=
    (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom.comp Algebra.TensorProduct.includeLeft
  let jR : κ' →ₐ[ℂ] T :=
    (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom.comp Algebra.TensorProduct.includeRight
  have hjL : ∀ e, (jL e : K ⊗[ℂ] κ') = (e : K) ⊗ₜ 1 := fun e => by
    simp [jL, tensMap]
  have hjR : ∀ c, (jR c : K ⊗[ℂ] κ') = 1 ⊗ₜ c := fun c => by
    simp [jR, tensMap]
  let ι : R →+* placeAlg E :=
    { toFun := fun r => ⟨r, hR _ r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hι : ∀ r : R, ((ι r : placeAlg E) : K) = r := fun _ => rfl

  have hg : ∀ r : R, jL (ι r) - jR (ρ (π r)) ∈ 𝔭 := fun r => by
    have e : ((jL (ι r) - jR (ρ (π r)) : T) : K ⊗[ℂ] κ') = (r : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π r) := by
      rw [Subalgebra.coe_sub, hjL (ι r), hjR (ρ (π r))]
      rfl
    exact hle (Ideal.subset_span (Or.inr ⟨r, e⟩))

  have hk : ∀ r : R, π r = 0 → q (jL (ι r)) = 0 := by
    intro r hr
    rw [hq0]
    apply Ideal.mem_sup_right
    by_cases h0 : (r : K) = 0
    · have e : jL (ι r) = 0 := Subtype.ext (by simp [hjL, hι, h0])
      rw [e]
      exact zero_mem _
    have hpos := (hord r h0).1 hr
    have hnu : ¬ IsUnit (⟨r, hR _ r.2⟩ : E.ring) := fun hu => by
      have h1 := E.ord_eq_zero hu
      simp only at h1
      omega
    have hm : (⟨r, hR _ r.2⟩ : E.ring) ∈ Ideal.span {t} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht]
      exact hnu
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hm
    rw [Ideal.mem_span_singleton']
    refine ⟨jL ⟨u, u.2⟩, Subtype.ext ?_⟩
    have hu' : (u : K) * t = r := congrArg Subtype.val hu
    simp only [Subalgebra.coe_mul, hjL, hι, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hu']

  have hu : ∀ r : R, π r ≠ 0 → IsUnit (q (jL (ι r))) := by
    intro r hr
    have hρ : IsUnit (q (jR (ρ (π r)))) :=
      ((isUnit_iff_ne_zero.2 ((map_ne_zero ρ).2 hr)).map jR).map q
    have hn : IsNilpotent (q (jL (ι r) - jR (ρ (π r)))) :=
      ⟨M, by rw [← map_pow, hq0]; exact Ideal.mem_sup_left (Ideal.pow_mem_pow (hg r) M)⟩
    have h := IsNilpotent.isUnit_add_left_of_commute hn hρ (Commute.all _ _)
    rwa [map_sub, add_sub_cancel] at h

  let φ : R →+* T ⧸ I := (q : T →+* T ⧸ I).comp ((jL : placeAlg E →+* T).comp ι)
  have hφ : ∀ r, φ r = q (jL (ι r)) := fun _ => rfl
  have hker : RingHom.ker π.rangeRestrict ≤ RingHom.ker φ := fun r hr => by
    rw [RingHom.mem_ker] at hr ⊢
    exact hk r (congrArg Subtype.val hr)
  let ψ : π.range →+* T ⧸ I :=
    π.rangeRestrict.liftOfRightInverse (Function.surjInv π.rangeRestrict_surjective)
      (Function.rightInverse_surjInv _) ⟨φ, hker⟩
  have hψ : ∀ r, ψ (π.rangeRestrict r) = q (jL (ι r)) := fun r =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ r
  haveI : IsFractionRing π.range κ := by
    refine ⟨fun y => ?_, fun z => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    · refine isUnit_iff_ne_zero.2 fun h => nonZeroDivisors.coe_ne_zero y (Subtype.ext h)
    · obtain ⟨c, d, hd, e⟩ := hfrac z
      exact ⟨(π.rangeRestrict c, ⟨π.rangeRestrict d, mem_nonZeroDivisors_of_ne_zero
        fun h => hd (congrArg Subtype.val h)⟩), e⟩
  have hunit : ∀ y : nonZeroDivisors π.range, IsUnit (ψ y) := by
    rintro ⟨⟨v, d, rfl⟩, hy⟩
    have hd : π d ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero ⟨_, hy⟩ (Subtype.ext h)
    exact (hψ d).symm ▸ hu d hd
  let θ₀ : κ →+* T ⧸ I := IsLocalization.lift (M := nonZeroDivisors π.range) hunit
  have hθ₀ : ∀ r, θ₀ (π r) = q (jL (ι r)) := fun r =>
    (IsLocalization.lift_eq (M := nonZeroDivisors π.range) hunit (π.rangeRestrict r)).trans (hψ r)

  let θ₀A : κ →ₐ[ℂ] T ⧸ I :=
    { θ₀ with
      commutes' := fun c => by
        have e1 : algebraMap ℂ κ c = π ⟨algebraMap ℂ K c, hC c⟩ := (hπC c (hC c)).symm
        have e2 : ι ⟨algebraMap ℂ K c, hC c⟩ = algebraMap ℂ (placeAlg E) c := Subtype.ext rfl
        change θ₀ (algebraMap ℂ κ c) = _
        rw [e1, hθ₀, e2, AlgHom.commutes, AlgHom.commutes] }
  let θ : κ ⊗[ℂ] κ' →ₐ[ℂ] T ⧸ I := Algebra.TensorProduct.productMap θ₀A (q.comp jR)
  have hθt : ∀ f c, θ (f ⊗ₜ c) = θ₀ f * q (jR c) := fun f c =>
    Algebra.TensorProduct.productMap_apply_tmul _ _ _ _

  have hwx : θ (∑ i, π (a i) ⊗ₜ[ℂ] b i) = q w := by
    have ew : w = ∑ i, jL (ι (a i)) * jR (b i) := by
      apply Subtype.ext
      rw [hw]
      simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_mul, hjL, hjR, hι,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [ew, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hθt, hθ₀, map_mul]

  have hgen : Ideal.map θ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ≤
      Ideal.map q 𝔭 := by
    refine (Ideal.map_mono (ker_productMap_le_span ρ)).trans ?_
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
    obtain ⟨c, d, hd, e⟩ := hfrac f
    have hfd : θ₀ f * q (jL (ι d)) = q (jL (ι c)) := by rw [← hθ₀, ← hθ₀, ← map_mul, e]
    set u := θ (f ⊗ₜ 1 - 1 ⊗ₜ ρ f) with hu_def
    have hu1 : u = θ₀ f - q (jR (ρ f)) := by
      rw [hu_def, map_sub, hθt, hθt]
      simp only [map_one, mul_one, one_mul]
    have h2 : u * q (jL (ι d)) =
        q (jL (ι c) - jR (ρ (π c))) - q (jR (ρ f)) * q (jL (ι d) - jR (ρ (π d))) := by
      rw [hu1, sub_mul, hfd, ← e, map_mul ρ, map_mul jR, map_sub q (jL (ι c)), map_sub q (jL (ι d)),
        map_mul q]
      rw [mul_sub, sub_sub_sub_cancel_right]
    have h3 : u * q (jL (ι d)) ∈ Ideal.map q 𝔭 := by
      rw [h2]
      exact sub_mem (Ideal.mem_map_of_mem q (hg c))
        (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem q (hg d)))
    obtain ⟨v, hv⟩ := (hu d hd).exists_right_inv
    have h4 : u = u * q (jL (ι d)) * v := by rw [mul_assoc, hv, mul_one]
    rw [SetLike.mem_coe, h4]
    exact Ideal.mul_mem_right _ _ h3
  have hbot : Ideal.map q 𝔭 ^ M = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro y hy
    rw [RingHom.mem_ker]
    exact (hq0 y).2 (Ideal.mem_sup_left hy)
  have h1 := Ideal.mem_map_of_mem θ hx
  rw [Ideal.map_pow] at h1
  have h2 := Ideal.pow_right_mono hgen M h1
  rw [hbot, Ideal.mem_bot] at h2
  exact (hq0 w).1 (hwx.symm.trans h2)

end GlobalTheory.GraphLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalvedSymplecticFormFiniteRealOrthogonal
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section
namespace GlobalTheory.WeilDatumF

theorem fst_symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h : y.map (infPartF F E) = 0 ∨ z.map (infPartF F E) = 0) : fstA F (symplOF σ JS JT ξ₀ y z) = 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.OrientedHeis.map_trace_hO_zero (fstA F) σ (incAF F E ξ₀) (fun a b => incAF F E (JS⁻¹ a b))
    (fun c d => incAF F E (JT c d)) y z h

theorem snd_symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h : y.map (finPartF F E) = 0 ∨ z.map (finPartF F E) = 0) : sndA F (symplOF σ JS JT ξ₀ y z) = 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.OrientedHeis.map_trace_hO_zero (sndA F) σ (incAF F E ξ₀) (fun a b => incAF F E (JS⁻¹ a b))
    (fun c d => incAF F E (JT c d)) y z h

theorem symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h1 : y.map (infPartF F E) = 0 ∨ z.map (infPartF F E) = 0)
    (h2 : y.map (finPartF F E) = 0 ∨ z.map (finPartF F E) = 0) : symplOF σ JS JT ξ₀ y z = 0 :=
  Prod.ext (fst_symplOF_eq_zero σ JS JT ξ₀ y z h1) (snd_symplOF_eq_zero σ JS JT ξ₀ y z h2)

theorem symplOHF_fin_real_orth (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (u x : WOF F E nS nT) :
      u.map (infPartF F E) = 0 → x.map (finPartF F E) = 0 → symplOHF σ JS JT ξ₀ u x = 0 ∧ symplOHF σ JS JT ξ₀ x u = 0 := by
  intro hu hx
  have e1 := symplOF_eq_zero σ JS JT ξ₀ u x (Or.inl hu) (Or.inr hx)
  have e2 := symplOF_eq_zero σ JS JT ξ₀ x u (Or.inr hu) (Or.inl hx)
  unfold symplOHF
  rw [e1, e2, mul_zero]
  exact ⟨rfl, rfl⟩

end GlobalTheory.WeilDatumF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralZeroStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTopFormChartIntegral_zero : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] (e : κ → OpenPartialHomeomorph Y (V n)) (S : Set Y), HasInt e (fun _ _ => 0) S 0 := by
  first | exact @GlobalTheory.GoodTop.hasInt_zero | exact GlobalTheory.GoodTop.hasInt_zero | (intros; apply GlobalTheory.GoodTop.hasInt_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeStableOfHeckeFramePolynomialActionStatement
section
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeStable_of_heckeFrame_polynomial_action : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)], F.IsHecke lam jK (NablaT F.O N lam) → F.IsHecke lam jK W → HeckeStable F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) ∧ HeckeNat F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) W := by
  first | exact @GlobalTheory.ExpFrame.heckeStable_heckeNat_of_isHecke | exact GlobalTheory.ExpFrame.heckeStable_heckeNat_of_isHecke | (intros; apply GlobalTheory.ExpFrame.heckeStable_heckeNat_of_isHecke <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFPreservesIsThetaFunctionStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperatorF_preserves_isThetaFunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ),
    Continuous ψ → ∀ (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ ψ f →
      IsThetaFunOF σ JS JT ξ₀ ψ (heisOF σ JS JT ξ₀ ψ w₀ f) := by
  first | exact @GlobalTheory.HeisKeepF.isThetaFunOF_heisOF | exact GlobalTheory.HeisKeepF.isThetaFunOF_heisOF | (intros; apply GlobalTheory.HeisKeepF.isThetaFunOF_heisOF <;> assumption)
end

