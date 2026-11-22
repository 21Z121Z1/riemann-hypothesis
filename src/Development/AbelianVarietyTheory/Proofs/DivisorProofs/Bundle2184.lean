import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2162
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingKrullDimQuotientMvPolynomialEqNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrOnOfNotFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStepFactorRatioUnitGaussSumQuotientStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaStepFactor_ratio_unit_gaussSumQuotient : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
      (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ), GlobalTheory.SqStep.BaseFits G W i j t Bs →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0 →
      GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  first | exact @GlobalTheory.SqStepArith.stepFac_ratio | exact GlobalTheory.SqStepArith.stepFac_ratio | (intros; apply GlobalTheory.SqStepArith.stepFac_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionVanishes
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ZeroDimSystem

def comb {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X} {m : ℕ}
    (t : Fin m → M.Sec) : (Fin m → k) →ₛₗ[algebraMap k Γ(X, ⊤)] M.Sec :=
  ⟨⟨fun c => ∑ i, algebraMap k Γ(X, ⊤) (c i) • t i, fun a b => by
      simp [add_smul, Finset.sum_add_distrib]⟩, fun c a => by
      simp [mul_smul, Finset.smul_sum]⟩

theorem comb_apply {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X} {m : ℕ}
    (t : Fin m → M.Sec) (c : Fin m → k) :
    comb t c = ∑ i, algebraMap k Γ(X, ⊤) (c i) • t i := rfl

def vanishAt {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X} {m : ℕ}
    (t : Fin m → M.Sec) (x : X) : Submodule k (Fin m → k) where
  carrier := {c | x ∉ nonzeroLocus (comb t c)}
  add_mem' := fun {a b} ha hb hx => by
    rw [map_add] at hx
    exact (nonzeroLocus_add_le _ _ hx).elim ha hb
  zero_mem' := fun hx => by
    rw [map_zero] at hx
    exact nonzeroLocus_secZero.le hx
  smul_mem' := fun c a ha hx => by
    rw [(comb t).map_smulₛₗ] at hx
    exact ha ((nonzeroLocus_secScale _ _).le hx).2

theorem mem_vanishAt {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X}
    {m : ℕ} (t : Fin m → M.Sec) (x : X) (c : Fin m → k) :
    c ∈ vanishAt t x ↔ x ∉ nonzeroLocus (comb t c) := Iff.rfl

theorem single_notMem_vanishAt {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    {M : LB X} {m : ℕ} (t : Fin m → M.Sec) {x : X} {i : Fin m} (hx : x ∈ nonzeroLocus (t i)) :
    (Pi.single i 1 : Fin m → k) ∉ vanishAt t x := by
  classical
  rw [mem_vanishAt, not_not, comb_apply,
    Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, map_one,
    one_smul]
  exact hx

section Main

variable {k : Type} [Field k] [Infinite k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
  [AlgebraicGeometry.IsNoetherian X] {M : LB X} (hM : M.IsLB) {m : ℕ} (t : Fin m → M.Sec)
  (ht : ⨆ i, nonzeroLocus (t i) = ⊤)
  (hf : ∀ r, algebraMap k Γ(X, ⊤) r = (strHom k X).appTop ((Scheme.ΓSpecIso (.of k)).inv r))
  (hp : IsProjOver (strHom k X))
include hM ht hf hp

end Main

end GlobalTheory.ZeroDimSystem

namespace GlobalTheory

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionDualNumberPointEqConstantCharZero
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsConst

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem ext_of_two {B C : Type} [CommRing B] [CommRing C] [IsLocalRing B] [IsLocalRing C]
    (d e : B →+* C) [IsLocalHom d] [IsLocalHom e] (hde : ∀ x y, d x = d y → e x = e y → x = y)
    {X : Scheme.{0}} (a b : Sp B ⟶ X) (h1 : spMap d ≫ a = spMap d ≫ b) (h2 : spMap e ≫ a = spMap e ≫ b) :
    a = b := by
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.surjective a
  obtain ⟨⟨y, g, hg⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.surjective b
  have l1 : ∀ (k : B →+* C) [IsLocalHom k] (φ : X.presheaf.stalk x ⟶ CommRingCat.of B),
      IsLocalHom φ.hom → IsLocalHom (φ ≫ CommRingCat.ofHom k).hom := by
    intro k _ φ _
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp k φ.hom
  have l2 : ∀ (k : B →+* C) [IsLocalHom k] (φ : X.presheaf.stalk y ⟶ CommRingCat.of B),
      IsLocalHom φ.hom → IsLocalHom (φ ≫ CommRingCat.ofHom k).hom := by
    intro k _ φ _
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp k φ.hom
  have key : ∀ (k : B →+* C) [IsLocalHom k], spMap k ≫ (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨x, f, hf⟩ =
      spMap k ≫ (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨y, g, hg⟩ →
      (⟨x, f ≫ CommRingCat.ofHom k, l1 k f hf⟩ : Σ z : X, {φ : X.presheaf.stalk z ⟶ CommRingCat.of C // IsLocalHom φ.hom}) =
        ⟨y, g ≫ CommRingCat.ofHom k, l2 k g hg⟩ := by
    intro k _ h
    apply (SpecToEquivOfLocalRing X (CommRingCat.of C)).symm.injective
    simpa [SpecToEquivOfLocalRing] using h
  have k1 := key d h1
  have k2 := key e h2
  obtain rfl : x = y := congrArg Sigma.fst k1
  have h5 : f ≫ CommRingCat.ofHom d = g ≫ CommRingCat.ofHom d :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj k1).2)
  have h6 : f ≫ CommRingCat.ofHom e = g ≫ CommRingCat.ofHom e :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj k2).2)
  obtain rfl : f = g := by
    ext s
    exact hde _ _ (congrArg (fun k => k.hom s) h5) (congrArg (fun k => k.hom s) h6)
  rfl

variable {K : Type} [Field K]

theorem isLocalRing_tsze (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    IsLocalRing (TrivSqZeroExt K M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

attribute [local instance] isLocalRing_tsze

theorem isLocalHom_map {M N : Type} [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N] [IsCentralScalar K N] (l : M →ₗ[K] N) :
    IsLocalHom (TrivSqZeroExt.map l).toRingHom :=
  ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] at ha ⊢
    simpa using ha⟩

abbrev ovO (B : Type) [CommRing B] [Algebra K B] : Over (Sp K) := Over.mk (spMap (algebraMap K B))

def ovH {B C : Type} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C] (φ : B →ₐ[K] C) :
    ovO (K := K) C ⟶ ovO B :=
  Over.homMk (spMap φ.toRingHom) (by
    simp only [ovO, Over.mk_hom]
    rw [sp_comp]
    congr 2
    exact φ.comp_algebraMap)

theorem ovH_left {B C : Type} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C] (φ : B →ₐ[K] C) :
    (ovH φ).left = spMap φ.toRingHom := rfl

theorem ovH_comp {B C E : Type} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C] [CommRing E] [Algebra K E]
    (φ : B →ₐ[K] C) (ψ : C →ₐ[K] E) : ovH (ψ.comp φ) = ovH ψ ≫ ovH φ := by
  ext1
  simp only [Over.comp_left, ovH_left, sp_comp]
  rfl

theorem ovH_id {B : Type} [CommRing B] [Algebra K B] : ovH (AlgHom.id K B) = 𝟙 (ovO B) := by
  ext1
  simp only [ovH_left, Over.id_left]
  exact Spec.map_id _

abbrev sc (t : K) : DualNumber K →ₐ[K] DualNumber K := TrivSqZeroExt.map (t • LinearMap.id)

abbrev jj (s t : K) : DualNumber K →ₐ[K] TrivSqZeroExt K (K × K) :=
  TrivSqZeroExt.map (LinearMap.prod (s • LinearMap.id) (t • LinearMap.id))

abbrev r1 : TrivSqZeroExt K (K × K) →ₐ[K] DualNumber K := TrivSqZeroExt.map (LinearMap.fst K K K)
abbrev r2 : TrivSqZeroExt K (K × K) →ₐ[K] DualNumber K := TrivSqZeroExt.map (LinearMap.snd K K K)
abbrev dd : TrivSqZeroExt K (K × K) →ₐ[K] DualNumber K := TrivSqZeroExt.map (LinearMap.fst K K K + LinearMap.snd K K K)

theorem dualNumberFirstProj_comp_twoEpsLinearComb (s t : K) : (r1 (K := K)).comp (jj s t) = sc s := by
  apply AlgHom.ext; intro x; ext <;> simp
theorem dualNumberSecondProj_comp_twoEpsLinearComb (s t : K) : (r2 (K := K)).comp (jj s t) = sc t := by
  apply AlgHom.ext; intro x; ext <;> simp
theorem dd_jj (s t : K) : (dd (K := K)).comp (jj s t) = sc (s + t) := by
  apply AlgHom.ext; intro x; ext <;> simp [add_mul]
theorem sc_sc (a b : K) : (sc a).comp (sc b) = sc (a * b) := by
  apply AlgHom.ext; intro x; ext <;> simp <;> ring
theorem sc_one : sc (1 : K) = AlgHom.id K _ := by
  apply AlgHom.ext; intro x; ext <;> simp

section Pts
variable {A : Over (Sp K)} [GrpObj A]

theorem ext2 (a b : ovO (K := K) (TrivSqZeroExt K (K × K)) ⟶ A) (h1 : ovH r1 ≫ a = ovH r1 ≫ b)
    (h2 : ovH r2 ≫ a = ovH r2 ≫ b) : a = b := by
  haveI := isLocalHom_map (K := K) (LinearMap.fst K K K)
  haveI := isLocalHom_map (K := K) (LinearMap.snd K K K)
  ext1
  refine ext_of_two (r1 (K := K)).toRingHom (r2 (K := K)).toRingHom ?_ a.left b.left
    (by simpa only [Over.comp_left, ovH_left] using congrArg CommaMorphism.left h1)
    (by simpa only [Over.comp_left, ovH_left] using congrArg CommaMorphism.left h2)
  intro x y hx hy
  have a1 := congrArg TrivSqZeroExt.fst hx
  have a2 := congrArg TrivSqZeroExt.snd hx
  have a3 := congrArg TrivSqZeroExt.snd hy
  simp at a1 a2 a3
  ext
  · exact a1
  · exact a2
  · exact a3

theorem hadd (hc : ∀ x y : ovO (K := K) (DualNumber K) ⟶ A, x * y = y * x) (x : ovO (DualNumber K) ⟶ A) (s t : K) :
    ovH (sc (s + t)) ≫ x * ovH (sc 0) ≫ x = ovH (sc s) ≫ x * ovH (sc t) ≫ x := by
  have e : ovH (jj s t) ≫ x * ovH (jj 0 0) ≫ x = ovH (jj s 0) ≫ x * ovH (jj 0 t) ≫ x := by
    apply ext2
    · simp only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dualNumberFirstProj_comp_twoEpsLinearComb]
    · simp only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dualNumberSecondProj_comp_twoEpsLinearComb]
      exact hc _ _
  have e2 := congrArg (fun z => ovH dd ≫ z) e
  simp only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dd_jj, add_zero, zero_add] at e2
  exact e2

end Pts

theorem eq_zeroScale_of_pow_eq_one_of_affine_fieldAction {G : Type} [CharZero K] [Group G] (hc : ∀ x y : G, x * y = y * x) (P : K → G → G)
    (hmul : ∀ t x y, P t (x * y) = P t x * P t y) (hcomp : ∀ a b x, P a (P b x) = P (a * b) x)
    (h1 : ∀ x, P 1 x = x) (hadd : ∀ s t x, P (s + t) x * P 0 x = P s x * P t x)
    (u : G) (n : ℕ) (hn : 0 < n) (hu : u ^ n = 1) : u = P 0 u := by
  letI : CommGroup G := { ‹Group G› with mul_comm := hc }
  have hone : ∀ t, P t 1 = 1 := fun t => mul_left_cancel (a := P t 1) (by rw [_root_.mul_one, ← hmul, _root_.one_mul])
  have hpow : ∀ t x (m : ℕ), P t (x ^ m) = P t x ^ m := by
    intro t x m
    induction m with
    | zero => simp [hone]
    | succ m ih => rw [pow_succ, hmul, ih, pow_succ]
  have step : ∀ m : ℕ, P m u * P 0 u ^ m = u ^ m * P 0 u := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hadd m 1 u
      rw [h1] at h
      rw [Nat.cast_succ, pow_succ', ← _root_.mul_assoc, h, mul_right_comm, ih, pow_succ]
      exact mul_right_comm _ _ _
  have e := step n
  rw [← hpow, hu, hone, _root_.mul_one, _root_.one_mul] at e
  calc u = P 1 u := (h1 u).symm
    _ = P ((n : K)⁻¹ * n) u := by rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')]
    _ = P (n : K)⁻¹ (P n u) := (hcomp _ _ _).symm
    _ = P (n : K)⁻¹ (P 0 u) := by rw [e]
    _ = P 0 u := by rw [hcomp, mul_zero]

end GlobalTheory.TorsConst

theorem GlobalTheory.TorsConst.torsion_eq_const : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (f : Sp (DualNumber K) ⟶ Sp K), f = spMap (algebraMap K (DualNumber K)) → (∀ x y : Over.mk f ⟶ A, x * y = y * x) → ∀ (u : Over.mk f ⟶ A) (n : ℕ), 0 < n → u ^ n = 1 → u.left = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left := by
  intro K _ _ A _ f hf hc u n hn hu
  subst hf
  open GlobalTheory.TorsConst in
  have key : u = ovH (sc 0) ≫ u :=
    eq_zeroScale_of_pow_eq_one_of_affine_fieldAction hc (fun t x => ovH (sc t) ≫ x) (fun t x y => MonObj.comp_mul _ _ _)
      (fun a b x => by simp only [← Category.assoc, ← ovH_comp, sc_sc])
      (fun x => by simp only [sc_one, ovH_id, Category.id_comp]) (fun s t x => hadd hc x s t) u n hn hu
  have e : (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom = (GlobalTheory.TorsConst.sc (0 : K)).toRingHom := by
    ext x <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [key]
  rw [Over.comp_left, GlobalTheory.TorsConst.ovH_left, ← e, ← Category.assoc, GlobalTheory.TorsConst.sp_comp]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHeckeOperatorSplitOnePlace
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.Peel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem globFn_eq (hU : Unr E) {S : Set (Pl E)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1) {w : Pl E} (hw : w ∈ S) (x : finU E n) :
    globFn S f x = f w (toSub _ (cLoc w x.1)) * ∏ᶠ u ∈ S \ {w}, f u (toSub _ (cLoc u x.1)) := by
  have hfin : (Function.mulSupport fun w : Pl E => f w (toSub (UL n w) (cLoc w (x : UA E n)))).Finite := by
    have h := (GlobalTheory.BCT.LocAE.eventually_mem_KL E hU n x).and hf
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    rintro u hu ⟨h1, h2⟩
    apply hu
    show f u _ = 1
    rw [h2, Set.indicator_of_mem (show _ ∈ (KL n u : Set (UL n u)) from h1)]
    rfl
  unfold globFn
  conv_lhs => rw [← Set.insert_diff_self_of_mem hw]
  exact finprod_mem_insert' _ (fun h => h.2 rfl) (hfin.subset Set.inter_subset_right)

theorem trOn_hop_peel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) * twTr σ.ρ (KL n w) (K' w) ((K' w : Set (UL n w)).indicator 1) LinearMap.id = twTr σ.ρ (KL n w) (K' w) (f w) LinearMap.id * trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (Function.update f w ((K' w : Set (UL n w)).indicator 1))) := by
  intro E _ _ _ hU n hn π hπ S hS K' hK' f hf w hw σ hσ
  obtain ⟨e, he⟩ := LocCompU.exists_equiv hU n w
  let ι : UL n w →* finU E n := (Subgroup.inclusion (inf_le_left : locU n w ≤ finU E n)).comp
    e.toMulEquiv.symm.toMonoidHom
  let r : finU E n →* UL n w := ((cLoc w).comp (finU E n).subtype).codRestrict _ fun x => GlobLev.cLoc_mem_UL w x.1
  have hιw : ∀ h, cLoc w (ι h).1 = h.1 := fun h => by
    change cLoc w ((e.symm h : locU n w) : UA E n) = _
    rw [← he, e.apply_symm_apply]
  have hιu : ∀ h, ∀ u ∈ S, u ≠ w → cLoc u (ι h).1 = 1 := fun h u hu huw => by
    obtain ⟨v, -, hv⟩ := hS w
    exact GlobalTheory.DefU.LocRet.mem_locU_ne (e.symm h).2 fun h' => huw ((hv u ⟨hu, h'⟩).trans (hv w ⟨hw, rfl⟩).symm)
  have hr : ∀ h, r (ι h) = h := fun h => Subtype.ext (hιw h)
  have hc : ∀ x ∈ r.ker, ∀ h, Commute x (ι h) := fun x hx h => by
    have h1 : cLoc w x.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 : GlobalTheory.DefU.LocRet.ret w n x.1 = 1 := by
      apply e.injective
      rw [map_one]
      refine Subtype.ext ((he _).trans ?_)
      exact (GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl x.1).trans h1
    have h3 := GlobalTheory.DefU.LocRet.commute_ret x.1 (e.symm h)
    rw [h2, OneMemClass.coe_one, inv_one, one_mul] at h3
    exact Subtype.ext h3.eq
  have hK1 : ∀ k ∈ K' w, ι k ∈ globLev S K' := fun k hk => (GlobLev.mem_globLev S K' _).2 fun u hu => by
    by_cases huw : u = w
    · subst huw
      have : (⟨cLoc u (ι k).1, GlobLev.cLoc_mem_UL u _⟩ : UL n u) = k := Subtype.ext (hιw k)
      rwa [this]
    · have : (⟨cLoc u (ι k).1, GlobLev.cLoc_mem_UL u _⟩ : UL n u) = 1 := Subtype.ext (hιu k u hu huw)
      rw [this]
      exact one_mem _
  have hK2 : ∀ k ∈ globLev S K', r k ∈ K' w := fun k hk => (GlobLev.mem_globLev S K' _).1 hk w hw
  obtain ⟨hind, h0, -⟩ := GlobalTheory.TwTrUnit.twTr_unit E n w (K' w) (hK'.1 w) σ
  set a' : UL n w → ℂ := (K' w : Set (UL n w)).indicator 1 with ha'
  have hf' : IsTest (KL n) K' (Function.update f w a') := by
    refine ⟨fun u => ?_, ?_⟩
    · by_cases huw : u = w
      · subst huw
        rwa [Function.update_self]
      · rw [Function.update_of_ne huw]
        exact hf.1 u
    · filter_upwards [hf.2, (Set.finite_singleton w).compl_mem_cofinite] with u h1 h2
      rwa [Function.update_of_ne h2]
  let b : r.ker → ℂ := fun x => ∏ᶠ u ∈ S \ {w}, f u (toSub _ (cLoc u x.1.1))
  have hsplit : ∀ g : ∀ u : Pl E, UL n u → ℂ, IsTest (KL n) K' g → (∀ u, u ≠ w → g u = f u) →
      ∀ h (x : r.ker), globFn S g (ι h * x) = g w h * b x := fun g hg hgf h x => by
    rw [globFn_eq hU hg.2 hw]
    have h1 : cLoc w x.1.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
    congr 1
    · rw [Subgroup.coe_mul, map_mul, hιw, h1, mul_one, toSub, dif_pos h.2]
    · refine finprod_mem_congr rfl fun u hu => ?_
      rw [hgf u hu.2, Subgroup.coe_mul, map_mul, hιu h u hu.1 hu.2, one_mul]
  have hF := hsplit f hf fun _ _ => rfl
  have hF' := hsplit _ hf' fun u hu => Function.update_of_ne hu _ _
  simp only [Function.update_self] at hF'
  have hH := GlobHecke.isHecke_globFn E hU n hn S hS K' hK' f hf
  have hH' := GlobHecke.isHecke_globFn E hU n hn S hS K' hK' _ hf'
  have hb : ∀ x : r.ker, b x = globFn S (Function.update f w a') x := fun x => by
    have := hF' 1 x
    rw [map_one, one_mul, ha', Set.indicator_of_mem (K' w).one_mem, Pi.one_apply, one_mul] at this
    exact this.symm
  have hopen := (GlobLev.globLev_isOpen_isCompact_isLevel E hU n hn S hS K' hK').2.2.1
  have hbfin : {q : r.ker ⧸ (globLev S K').subgroupOf r.ker | b q.out ≠ 0}.Finite := by
    refine Set.Finite.of_finite_image (f := fun q => (((q.out : r.ker) : finU E n) : finU E n ⧸ globLev S K'))
      ((GlobalTheory.TwTrLin.finite_out_support hopen hH'.1).subset ?_) fun p _ q _ h => ?_
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (globLev S K') ((q.out : r.ker) : finU E n)
      change globFn S _ _ ≠ 0
      rw [hk, (hH'.2 _ k.2 _).2, ← hb]
      exact hq
    · have h' : ((((p.out : r.ker) : finU E n)) : finU E n ⧸ globLev S K') = ((q.out : r.ker) : finU E n) := h
      rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]
      refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
      have := QuotientGroup.eq.1 h'
      simpa using this
  haveI := σ.irred
  have hiso : π ≤ LocUniq.isoPart σ.ρ ((RF E n).comp ι) := by
    obtain ⟨p, hp, -, φ, hφ0, hφm, hφ⟩ := hσ
    have hpe : ∀ g, p (e.symm g) = g := fun g => Subtype.ext ((hp _).trans (hιw g))
    let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
    let s : UL n w →* UA E n := (finU E n).subtype.comp ι
    let Φ : σ.ρ.IntertwiningMap (π'.rep.comp s) :=
      ⟨φ.codRestrict π hφm, fun g => LinearMap.ext fun v => Subtype.ext (by
        have := hφ (e.symm g) v
        rw [hpe] at this
        exact this)⟩
    have hΦ0 : Φ ≠ 0 := fun h =>
      hφ0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    obtain ⟨h1, -⟩ := GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (UL n w) π σ.V σ.V π'.rep s σ.ρ σ.ρ π'.isIrreducible_rep
      σ.irred σ.irred (fun g => ⟨e (GlobalTheory.DefU.LocRet.ret w n g), fun y => by
        have h3 := GlobalTheory.DefU.LocRet.commute_ret g (e.symm y)
        have h4 : s (e (GlobalTheory.DefU.LocRet.ret w n g)) = GlobalTheory.DefU.LocRet.ret w n g := by
          change ((e.symm (e _) : locU n w) : UA E n) = _
          rw [e.symm_apply_apply]
        rw [h4]
        exact h3⟩) Φ hΦ0
    intro v hv
    have hle : (⨆ ψ : σ.ρ.IntertwiningMap (π'.rep.comp s), LinearMap.range ψ.toLinearMap) ≤
        (LocUniq.isoPart σ.ρ ((RF E n).comp ι)).comap π.subtype := by
      refine iSup_le fun ψ => ?_
      rintro _ ⟨u, rfl⟩
      exact Submodule.mem_iSup_of_mem (⟨π.subtype ∘ₗ ψ.toLinearMap, fun g => LinearMap.ext fun y =>
        congrArg Subtype.val (LinearMap.congr_fun (ψ.isIntertwining' g) y)⟩ :
          σ.ρ.IntertwiningMap ((RF E n).comp ι)) ⟨u, rfl⟩
    rw [h1] at hle
    exact hle (Submodule.mem_top : (⟨v, hv⟩ : π) ∈ ⊤)
  exact trOn_levOp_cross ι r hr hc hK1 hK2 (RF E n) π (fun g v hv => hπ.stable _ v hv) σ.ρ hiso _ (KL n w) h0 _ _
    (f w) a' b hF hF' (fun k hk x => (hH.2 k hk x).2) (fun k hk x => (hH'.2 k hk x).2) (hf.1 w).2 hind.2
    (fun k hk x => by
      rw [hb, hb, hb]
      exact hH'.2 _ hk _)
    (GlobalTheory.TwTrLin.finite_out_support (hK'.1 w).1 (hf.1 w).1) (GlobalTheory.TwTrLin.finite_out_support (hK'.1 w).1 hind.1) hbfin

end GlobalTheory.BCT.Peel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwSecMulPow
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatTw.TwSec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c}

theorem exists_pow {G₀ : WTZ E} (s : TwSec U x Z G₀) (n : ℕ) :
    ∃ u : TwSec U x Z (n • G₀), u.lo = n • s.lo ∧ u.degLo = n * s.degLo := by
  induction n with
  | zero =>
    obtain ⟨-, -, h2, -, h3⟩ := const_spec (x := x) s.pts (1 : c.F) one_ne_zero
    refine ⟨(const x s.pts 1 one_ne_zero).copy (zero_nsmul G₀).symm, ?_, ?_⟩
    · funext w
      show (const x s.pts 1 one_ne_zero).lo w = _
      rw [h2 w]
      simp [vAdd]
    · show (const x s.pts 1 one_ne_zero).degLo = _
      rw [h3]; simp
  | succ n ih =>
    obtain ⟨u, hl, hd⟩ := ih
    refine ⟨(u.mul s).copy (succ_nsmul G₀ n).symm, ?_, ?_⟩
    · show u.lo + s.lo = _
      rw [hl, succ_nsmul]
    · show (u.mul s).degLo = _
      rw [degLo_mul, hd]; push_cast; ring

end GlobalTheory.FlatTw.TwSec

theorem GlobalTheory.FlatTw.twSec_mul_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c), (∀ (G₀ G₁ : WTZ E) (s : TwSec U x Z G₀) (t : TwSec U x Z G₁), ∃ u : TwSec U x Z (G₀ + G₁), u.sig = s.sig * t.sig ∧ u.cInf = s.cInf * t.cInf ∧ u.lo = s.lo + t.lo ∧ u.degLo = s.degLo + t.degLo) ∧ ∀ (G₀ : WTZ E) (s : TwSec U x Z G₀) (n : ℕ), ∃ u : TwSec U x Z (n • G₀), u.lo = n • s.lo ∧ u.degLo = n * s.degLo := by
  intro E _ _ _ H Dw l Xo c r U x Z
  exact ⟨fun G₀ G₁ s t => ⟨s.mul t, rfl, rfl, rfl, TwSec.degLo_mul s t⟩, fun G₀ s n => s.exists_pow n⟩
end
end

