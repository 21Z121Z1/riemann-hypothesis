import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0667
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.IsFractionRingIntO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TmulEqZeroOfMemSmulTop
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open scoped TensorProduct
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.TotalFrame

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineSummand

variable {O X k : Type} [CommRing O] [AddCommGroup X] [Module O X] [Field k] {p : ℕ} [CharP k p]

theorem tmul_nsmul_eq_zero (c : k) (y : X) : c ⊗ₜ[ℤ] (p • y) = 0 := by
  show (TensorProduct.mk ℤ k X c) (p • y) = 0
  rw [map_nsmul, TensorProduct.mk_apply, TensorProduct.smul_tmul', nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
    TensorProduct.zero_tmul]

theorem tmul_eq_zero_of_mem_smul_top {x : X} (hx : x ∈ (Ideal.span {(p : O)} • ⊤ : Submodule O X)) (c : k) :
    c ⊗ₜ[ℤ] x = 0 := by
  refine Submodule.smul_induction_on (p := fun x => c ⊗ₜ[ℤ] x = 0) hx (fun r hr n _ => ?_) fun x y hx hy => ?_
  · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    have e : (a * (p : O)) • n = p • (a • n) := by rw [mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
    rw [e]
    exact tmul_nsmul_eq_zero c _
  · simp only [TensorProduct.tmul_add, hx, hy, add_zero]

variable (k) in

theorem baseChange_mkQ_injective (P : Submodule O X) (hP : ∀ x ∈ P, ∀ c : k, c ⊗ₜ[ℤ] x = 0) :
    Function.Injective ((P.mkQ.restrictScalars ℤ).baseChange k) := by
  let g : X →ₗ[ℤ] X ⧸ P := P.mkQ.restrictScalars ℤ
  have hex := lTensor_exact k (LinearMap.exact_subtype_ker_map g) P.mkQ_surjective
  rw [LinearMap.baseChange_eq_ltensor]
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨z, rfl⟩ := (hex y).1 hy
  clear hy
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    rw [LinearMap.lTensor_tmul]
    exact hP _ ((Submodule.Quotient.mk_eq_zero P).1 (LinearMap.mem_ker.1 x.2)) c
  | add u v hu hv => rw [map_add, hu, hv, add_zero]

end GlobalTheory.LineSummand

namespace GlobalTheory.LineSummand

variable {O X k : Type} [CommRing O] [AddCommGroup X] [Module O X] [Field k] {p : ℕ} [CharP k p]

variable (k) in

theorem line_summand (P : Submodule O X) (hPz : ∀ x ∈ P, ∀ c : k, c ⊗ₜ[ℤ] x = 0) (l l' : Submodule O (X ⧸ P))
    (h : IsCompl l l')
    (e : l ≃ₗ[O] (O ⧸ Ideal.span {(p : O)})) :
    ∃ (M' : Submodule k (k ⊗[ℤ] X)) (n₀ : k ⊗[ℤ] X),
      IsCompl (Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ l ∧ s = 1 ⊗ₜ a}) M' ∧
      (∀ a, ∀ x ∈ Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ l ∧ s = 1 ⊗ₜ a},
        baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X) a x ∈
          Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ l ∧ s = 1 ⊗ₜ a}) ∧
      (∀ a, ∀ x ∈ M', baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X) a x ∈ M') ∧
      Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ l ∧ s = 1 ⊗ₜ a} =
        Submodule.span k (Set.range fun a => baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X) a n₀) ∧
      ∀ t : k ⊗[ℤ] O, tensorAction (baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X)) t n₀ = 0 → t = 0 := by
  set ρb : O →+* Module.End k (k ⊗[ℤ] X) := baseChangeAction k (Module.toModuleEnd ℤ X : O →+* Module.End ℤ X)
  let bar : Submodule O (X ⧸ P) → Submodule k (k ⊗[ℤ] X) := fun m =>
    Submodule.span k {s | ∃ a : X, Submodule.Quotient.mk a ∈ m ∧ s = 1 ⊗ₜ a}
  have hρ : ∀ (a : O) (c : k) (x : X), ρb a (c ⊗ₜ x) = c ⊗ₜ (a • x) := fun a c x => by
    simp [ρb, baseChangeAction_apply, LinearMap.baseChange_tmul]
  have hz : ∀ x ∈ P, (1 : k) ⊗ₜ[ℤ] x = 0 := fun x hx => hPz x hx 1

  have hst : ∀ (m : Submodule O (X ⧸ P)) (a : O), ∀ x ∈ bar m, ρb a x ∈ bar m := by
    intro m a x hx
    refine (Submodule.span_le (p := (bar m).comap (ρb a))).2 (fun s hs => ?_) hx
    obtain ⟨b, hb, rfl⟩ := hs
    show ρb a (1 ⊗ₜ b) ∈ bar m
    rw [hρ]
    exact Submodule.subset_span ⟨a • b, by rw [Submodule.Quotient.mk_smul]; exact m.smul_mem a hb, rfl⟩

  have htop : bar l ⊔ bar l' = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul c a =>
      have e1 : c ⊗ₜ[ℤ] a = c • ((1 : k) ⊗ₜ[ℤ] a) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1]
      refine Submodule.smul_mem _ c ?_
      have hm : (Submodule.Quotient.mk a : X ⧸ P) ∈ l ⊔ l' := h.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨u, hu, u', hu', e2⟩ := Submodule.mem_sup.1 hm
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective P u
      obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective P u'
      have hd : a - b - b' ∈ P := by
        rw [← Submodule.Quotient.mk_eq_zero P, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, ← e2]
        abel
      have e3 : (1 : k) ⊗ₜ[ℤ] a = 1 ⊗ₜ b + 1 ⊗ₜ b' + 1 ⊗ₜ (a - b - b') := by
        rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_add]
        congr 1
        abel
      rw [e3, hz _ hd, add_zero]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨b, hu, rfl⟩) (Submodule.subset_span ⟨b', hu', rfl⟩)
    | add x y hx hy => exact add_mem hx hy

  let π : X →ₗ[ℤ] X ⧸ P := P.mkQ.restrictScalars ℤ
  let proj : (X ⧸ P) →ₗ[O] l := LinearMap.ofIsCompl h LinearMap.id 0
  let q : X →ₗ[ℤ] l := (proj ∘ₗ P.mkQ).restrictScalars ℤ
  let ls : l →ₗ[ℤ] X ⧸ P := l.subtype.restrictScalars ℤ
  have hπ : Function.Injective (π.baseChange k) :=
    baseChange_mkQ_injective k P hPz
  have h1 : bar l ≤ LinearMap.eqLocus (π.baseChange k) ((ls.baseChange k) ∘ₗ (q.baseChange k)) := by
    refine Submodule.span_le.2 fun s hs => ?_
    obtain ⟨b, hb, rfl⟩ := hs
    show π.baseChange k (1 ⊗ₜ b) = ls.baseChange k (q.baseChange k (1 ⊗ₜ b))
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    congr 1
    show Submodule.Quotient.mk b = ((proj (Submodule.Quotient.mk b) : l) : X ⧸ P)
    have := LinearMap.ofIsCompl_apply_left h (φ := LinearMap.id) (ψ := 0) ⟨_, hb⟩
    exact (congrArg Subtype.val this).symm
  have h2 : bar l' ≤ LinearMap.ker (q.baseChange k) := by
    refine Submodule.span_le.2 fun s hs => ?_
    obtain ⟨b, hb, rfl⟩ := hs
    show q.baseChange k (1 ⊗ₜ b) = 0
    rw [LinearMap.baseChange_tmul]
    have := LinearMap.ofIsCompl_apply_right h (φ := LinearMap.id) (ψ := 0) ⟨_, hb⟩
    show (1 : k) ⊗ₜ[ℤ] proj (Submodule.Quotient.mk b) = 0
    rw [this, LinearMap.zero_apply, TensorProduct.tmul_zero]
  have hcompl : IsCompl (bar l) (bar l') := by
    refine ⟨Submodule.disjoint_def.2 fun x hx hx' => hπ ?_, codisjoint_iff.2 htop⟩
    rw [LinearMap.mem_eqLocus.1 (h1 hx), LinearMap.comp_apply, LinearMap.mem_ker.1 (h2 hx'), map_zero, map_zero]

  obtain ⟨a₀, ha₀⟩ := Submodule.Quotient.mk_surjective P (e.symm 1 : X ⧸ P)
  have hmk : ∀ c : O, (Submodule.Quotient.mk (c • a₀) : X ⧸ P) = (e.symm (Ideal.Quotient.mk _ c) : X ⧸ P) := by
    intro c
    have : (Ideal.Quotient.mk (Ideal.span {(p : O)}) c) = c • 1 := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [Submodule.Quotient.mk_smul, ha₀, this, map_smul, Submodule.coe_smul]
  refine ⟨bar l', 1 ⊗ₜ a₀, hcompl, hst l, hst l', le_antisymm ?_ ?_, ?_⟩
  · refine Submodule.span_le.2 fun s hs => ?_
    obtain ⟨b, hb, rfl⟩ := hs
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (e ⟨_, hb⟩)
    have hd : b - c • a₀ ∈ P := by
      rw [← Submodule.Quotient.mk_eq_zero P, Submodule.Quotient.mk_sub, hmk, hc, LinearEquiv.symm_apply_apply, sub_self]
    have e4 : (1 : k) ⊗ₜ[ℤ] b = ρb c (1 ⊗ₜ a₀) + 1 ⊗ₜ (b - c • a₀) := by
      rw [hρ, ← TensorProduct.tmul_add, add_sub_cancel]
    rw [SetLike.mem_coe, e4, hz _ hd, add_zero]
    exact Submodule.subset_span ⟨c, rfl⟩
  · refine Submodule.span_le.2 fun s hs => ?_
    obtain ⟨c, rfl⟩ := hs
    show ρb c (1 ⊗ₜ a₀) ∈ bar l
    rw [hρ]
    exact Submodule.subset_span ⟨c • a₀, by rw [hmk]; exact (e.symm _).2, rfl⟩
  ·
    let fA : O →ₗ[ℤ] X := (LinearMap.toSpanSingleton O X a₀).restrictScalars ℤ
    have hT : ∀ t, tensorAction ρb t (1 ⊗ₜ a₀) = fA.baseChange k t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul c a =>
        rw [tensorAction_tmul, hρ, LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rfl
      | add s t hs ht => rw [map_add, LinearMap.add_apply, hs, ht, map_add]
    let mO : O →ₗ[ℤ] O ⧸ Ideal.span {(p : O)} := (Submodule.mkQ (Ideal.span {(p : O)})).restrictScalars ℤ
    let es : (O ⧸ Ideal.span {(p : O)}) →ₗ[ℤ] l := (e.symm : (O ⧸ Ideal.span {(p : O)}) →ₗ[O] l).restrictScalars ℤ
    have key : ∀ t, π.baseChange k (fA.baseChange k t) = ls.baseChange k (es.baseChange k (mO.baseChange k t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul c a =>
        simp only [LinearMap.baseChange_tmul]
        congr 1
        exact hmk a
      | add s t hs ht => simp only [map_add, hs, ht]
    have hmO : Function.Injective (mO.baseChange k) := by
      refine baseChange_mkQ_injective k (Ideal.span {(p : O)}) fun x hx c => ?_
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      have e5 : a * (p : O) = p • a := by rw [mul_comm, ← nsmul_eq_mul]
      rw [e5]
      exact tmul_nsmul_eq_zero c a
    have hes : Function.Injective (es.baseChange k) := by
      refine Function.LeftInverse.injective (g := ((e : l →ₗ[O] O ⧸ Ideal.span {(p : O)}).restrictScalars ℤ).baseChange k)
        fun y => ?_
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c u => simp [es]
      | add s t hs ht => simp only [map_add, hs, ht]
    have hls : Function.Injective (ls.baseChange k) := by
      refine Function.LeftInverse.injective (g := (proj.restrictScalars ℤ).baseChange k) fun y => ?_
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c u =>
        simp only [LinearMap.baseChange_tmul]
        congr 1
        exact LinearMap.ofIsCompl_apply_left h (φ := LinearMap.id) (ψ := 0) u
      | add s t hs ht => simp only [map_add, hs, ht]
    intro t ht
    rw [hT] at ht
    have h0 : ls.baseChange k (es.baseChange k (mO.baseChange k t)) = 0 := by rw [← key, ht, map_zero]
    exact (injective_iff_map_eq_zero _).1 hmO _ ((injective_iff_map_eq_zero _).1 hes _
      ((injective_iff_map_eq_zero _).1 hls _ h0))

end GlobalTheory.LineSummand

namespace GlobalTheory.LineSummand

theorem sum1_bar_line : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p) (l : ct.Sum1),
  ∃ (M' : Submodule ct.kbar ct.LaBar) (n₀ : ct.LaBar), IsCompl l.bar M' ∧
    (∀ a, ∀ x ∈ l.bar, (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) a x ∈ l.bar) ∧ (∀ a, ∀ x ∈ M', (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) a x ∈ M') ∧
    l.bar = Submodule.span ct.kbar (Set.range fun a => (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) a n₀) ∧
    ∀ t : ct.kbar ⊗[ℤ] 𝓞 D.host.E, tensorAction (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) t n₀ = 0 → t = 0 := by
  intro D A N j S κ p ct l
  obtain ⟨l', hl'⟩ := l.2.1
  obtain ⟨e⟩ := l.2.2
  exact line_summand ct.kbar _ (fun x hx c => tmul_eq_zero_of_mem_smul_top (p := p) hx c) l.1 l' hl' e

end GlobalTheory.LineSummand
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharEqOfEqOnTorsion
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj

namespace GlobalTheory.CharUniq

attribute [local instance] Over.cartesianMonoidalCategory

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem exists_restr {T T' : Scheme.{0}} (g : T' ⟶ T) (p : T ⟶ X) (p' : T' ⟶ X) (h : g ≫ p = p') :
    ∃ r : (Over.mk p ⟶ t.G) →* (Over.mk p' ⟶ t.G), ∀ w, (r w).left = g ≫ w.left := by
  let δ : Over.mk p' ⟶ Over.mk p := Over.homMk g h
  exact ⟨{ toFun := fun w => δ ≫ w, map_one' := by simp, map_mul' := fun a b => comp_mul _ _ _ }, fun w => rfl⟩

theorem isFinPart_of_equiv {R L B : Type} [CommRing R] [CommRing L] [CommRing B] [Algebra R B] [Algebra L B]
    (e : R ≃+* L) (he : (algebraMap L B).comp e.toRingHom = algebraMap R B) (x : Sp R ⟶ X) (q : ℕ)
    (u : Over.mk (spMap (algebraMap L B) ≫ spMap e.toRingHom ≫ x) ⟶ t.G)
    (u' : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G) (hu : u'.left = u.left)
    (h : IsFinPart t (spMap e.toRingHom ≫ x) q u) : IsFinPart t x q u' := by
  have he' : (algebraMap R B).comp e.symm.toRingHom = algebraMap L B := by
    rw [← he]; ext a; simp
  have th : ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Sp S ⟶ t.G.left),
      Thru t u'.left φ w ↔ Thru t u.left (φ.comp e.symm.toRingHom) w := by
    intro S _ φ w
    rw [hu]
    refine exists_congr fun β => and_congr_left fun _ => ⟨fun a => ?_, fun a => ?_⟩
    · rw [← a, RingHom.comp_assoc, he']
    · rw [← he, ← RingHom.comp_assoc, a]; ext b; simp
  have tr : ∀ (S : Type) [CommRing S] (φ : R →+* S),
      ∃ r : (Over.mk (spMap φ ≫ x) ⟶ t.G) →* (Over.mk (spMap (φ.comp e.symm.toRingHom) ≫ spMap e.toRingHom ≫ x) ⟶ t.G),
        ∀ w, (r w).left = w.left := by
    intro S _ φ
    obtain ⟨r, hr⟩ := exists_restr t (𝟙 _) (spMap φ ≫ x)
      (spMap (φ.comp e.symm.toRingHom) ≫ spMap e.toRingHom ≫ x) (by
        rw [Category.id_comp, ← Category.assoc, spc]
        congr 2; ext b; simp)
    exact ⟨r, fun w => (hr w).trans (Category.id_comp _)⟩
  letI : Algebra R L := e.toRingHom.toAlgebra
  haveI : IsScalarTower R L B := IsScalarTower.of_algebraMap_eq' he.symm
  let e' : R ≃ₐ[R] L := AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  haveI := h.finite
  haveI := h.free
  haveI : Module.Finite R L := Module.Finite.equiv e'.toLinearEquiv
  haveI : Module.Free R L := Module.Free.of_equiv e'.toLinearEquiv
  refine ⟨Module.Finite.trans L B, Module.Free.trans (S := L), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := exists_restr t (𝟙 _) (spMap (algebraMap L B) ≫ spMap e.toRingHom ≫ x)
      (spMap (algebraMap R B) ≫ x) (by rw [Category.id_comp, ← Category.assoc, spc, he])
    have : u' = r u := Over.OverMorphism.ext (by rw [hr, hu]; exact (Category.id_comp _).symm)
    rw [this, ← map_pow, h.tors, map_one]
  · intro S _ β β' h1 h2
    refine h.mono S β β' (by rw [← he', ← RingHom.comp_assoc, h1, RingHom.comp_assoc]) (by rw [← hu]; exact h2)
  · intro S _ φ w hw hm
    obtain ⟨r, hr⟩ := tr S φ
    rw [th, ← hr]
    refine h.isOpen S _ (r w) (by rw [← map_pow, hw, map_one]) fun 𝔪 h𝔪 => ?_
    rw [hr]
    exact (th _ _ _).1 (hm 𝔪 h𝔪)
  · intro S _ φ
    obtain ⟨r, hr⟩ := tr S φ
    rw [th, ← hr, map_one]
    exact h.one S _
  · intro S _ φ w w' h1 h2
    obtain ⟨r, hr⟩ := tr S φ
    rw [th, ← hr] at h1 h2 ⊢
    rw [map_mul]
    exact h.mul S _ _ _ h1 h2
  · intro k _ β
    obtain ⟨σ, hσ⟩ := h.sect k β
    refine ⟨e'.symm.toAlgHom.comp (σ.restrictScalars R), hσ.trans ?_⟩
    rw [← he']
    rfl
  · intro b hb
    refine h.inj b fun σ => ?_
    have := hb (e'.symm.toAlgHom.comp (σ.restrictScalars R))
    exact e'.symm.injective (this.trans (map_zero _).symm)

theorem exists_finPart_local [IsLocallyNoetherian X] (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CharZero R] [IsLocalRing R] (x : Sp R ⟶ X) (q : ℕ) (hq : q ≠ 0) (hs : SplitTors t x q) :
    ∃ (B₀ : Type) (_ : CommRing B₀) (_ : Algebra R B₀) (u : Over.mk (spMap (algebraMap R B₀) ≫ x) ⟶ t.G),
      IsFinPart t x q u ∧ ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B]
        (w : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G), w ^ q = 1 → Thru t u.left (algebraMap R B) w.left := by
  obtain ⟨f, B₀, _, _, u, hf, hu, hk⟩ := GlobalTheory.T.exists_local_finite_torsion_splitting E H X t R x q hq hs (IsLocalRing.maximalIdeal R) inferInstance
  have hfu : IsUnit f := by
    by_contra hn
    exact hf hn
  let e : R ≃+* Localization.Away f :=
    (IsLocalization.atUnits R (Submonoid.powers f) (S := Localization.Away f)
      ((Submonoid.powers_le).2 hfu)).toRingEquiv
  have hee : e.toRingHom = algebraMap R (Localization.Away f) := by
    ext a
    exact (IsLocalization.atUnits R (Submonoid.powers f) (S := Localization.Away f)
      ((Submonoid.powers_le).2 hfu)).commutes a
  letI : Algebra R B₀ := ((algebraMap (Localization.Away f) B₀).comp e.toRingHom).toAlgebra
  revert u
  rw [← hee]
  intro u hu hk
  obtain ⟨r, hr⟩ := exists_restr t (𝟙 _) (spMap (algebraMap (Localization.Away f) B₀) ≫ spMap e.toRingHom ≫ x)
    (spMap (algebraMap R B₀) ≫ x) (by rw [Category.id_comp, ← Category.assoc, spc])
  have hr' : (r u).left = u.left := (hr u).trans (Category.id_comp _)
  have hu' := isFinPart_of_equiv t e rfl x q u (r u) hr' hu
  refine ⟨B₀, inferInstance, inferInstance, r u, hu', fun B _ _ _ w hw => hu'.isOpen B _ w hw fun 𝔪 h𝔪 => ?_⟩
  letI := Ideal.Quotient.field 𝔪
  let φ : R →+* B ⧸ 𝔪 := (Ideal.Quotient.mk 𝔪).comp (algebraMap R B)
  have hφ : (φ.comp e.symm.toRingHom).comp e.toRingHom = φ := by ext a; simp
  obtain ⟨s, hs⟩ := exists_restr t (spMap (Ideal.Quotient.mk 𝔪)) (spMap (algebraMap R B) ≫ x)
    (spMap (φ.comp e.symm.toRingHom) ≫ spMap e.toRingHom ≫ x) (by
      rw [← Category.assoc, ← Category.assoc, spc, spc, hφ])
  obtain ⟨β, h1, h2⟩ := hk (B ⧸ 𝔪) (φ.comp e.symm.toRingHom) (by
    rw [hφ]
    have : (𝔪.comap (algebraMap R B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔪
    rw [← IsLocalRing.eq_maximalIdeal this, ← RingHom.comap_ker, Ideal.mk_ker]) (s w)
    (by rw [← map_pow, hw, map_one])
  refine ⟨β, ?_, by rw [hr', h2, hs]⟩
  exact (congrArg (fun z => z.comp e.toRingHom) h1).trans hφ

theorem exists_finPart_int [IsLocallyNoetherian X] (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q : ℕ) (hq : q ≠ 0) :
    ∃ (B₀ : Type) (_ : CommRing B₀) (_ : Algebra ↥(intO C) B₀)
      (u : Over.mk (spMap (algebraMap ↥(intO C) B₀) ≫ x) ⟶ t.G),
      IsFinPart t x q u ∧ ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B]
        (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 →
          Thru t u.left (algebraMap ↥(intO C) B) w.left := by
  haveI := GlobalTheory.IntegralPointCheck.valuationRing_intO C
  haveI := GlobalTheory.IntegralPointCheck.isFractionRing_intO C
  haveI : IsAlgClosed (FractionRing ↥(intO C)) :=
    IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv ↥(intO C) C).symm.toRingEquiv
  exact exists_finPart_local t _ x q hq (GlobalTheory.T.splitTors_algClosed_fraction_field E H X t _ x q hq)

theorem char_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q : ℕ), q ≠ 0 → ∀ c c' : TorsChar t x q, (∀ w : Over.mk (spMap (algebraMap ↥(intO C) ↥(intO C)) ≫ x) ⟶ t.G, w ^ q = 1 → c.χ ↥(intO C) w = c'.χ ↥(intO C) w) → ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B] (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 → c.χ B w = c'.χ B w := by
  intro E _ _ _ H X _ t C _ _ _ _ x q hq c c' h B _ _ _ w hw
  obtain ⟨B₀, _, _, u, hu, hth⟩ := exists_finPart_int t C x q hq
  haveI := hu.finite
  have key : (c.χ B₀ u : B₀) = c'.χ B₀ u := by
    refine sub_eq_zero.1 (hu.inj _ fun σ => ?_)
    obtain ⟨r, hr⟩ := exists_restr t (spMap σ.toRingHom) (spMap (algebraMap ↥(intO C) B₀) ≫ x)
      (spMap (algebraMap ↥(intO C) ↥(intO C)) ≫ x) (by
        rw [← Category.assoc, spc]
        congr 2
        exact RingHom.ext fun a => σ.commutes a)
    rw [map_sub, ← c.nat B₀ _ σ u (r u) hu.tors (hr u), ← c'.nat B₀ _ σ u (r u) hu.tors (hr u),
      h (r u) (by rw [← map_pow, hu.tors, map_one]), sub_self]
  obtain ⟨β, h1, h2⟩ := hth B w hw
  let β' : B₀ →ₐ[↥(intO C)] B := { β with commutes' := fun a => RingHom.congr_fun h1 a }
  refine Units.ext ?_
  rw [c.nat B₀ B β' u w hu.tors h2.symm, c'.nat B₀ B β' u w hu.tors h2.symm, key]

end GlobalTheory.CharUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationExpansionSumsEqTransport
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR in
set_option maxHeartbeats 1600000 in

theorem expansion_sums_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ (σ : H0 U.LG.L 2) (σ' : H0 U'.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') → (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') → ∀ e : ℕ, ∃ S : Finset D'.toPre.X, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → (∀ α' ∉ S, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J = 0) ∧ (∀ α' ∉ S, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' = 0) ∧ ∑ α' ∈ S, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)).val * ∑ α' ∈ S, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val := by
  intro R _ _ _ _ G _ _ _ D D' A A' U U' Φ w wL _ _ _ hlev xe _ σ σ' f f' hE hE' hσ e
  classical
  obtain ⟨S₁, hS₁⟩ := expandsAt_val U.toUnifPre e 2 σ f (hE e)
  obtain ⟨S₂, hS₂⟩ := expandsAt_val U'.toUnifPre e 2 σ' f' (hE' e)
  refine ⟨S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂, fun Z r z J J' hJ hJ' => ?_⟩
  obtain ⟨A₁, B₁⟩ := hS₁ Z r z J hJ
  obtain ⟨A₂, B₂⟩ := hS₂ Z r z J' hJ'
  have z₁ : ∀ α' ∉ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J = 0 := by
    intro α' hα
    refine A₁ _ fun hc => hα (Finset.mem_union_left _ (Finset.mem_map.2 ⟨xe α', hc, xe.symm_apply_apply α'⟩))
  have z₂ : ∀ α' ∉ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f' α') (r ≫ (U'.gt e).pG.left) z J' = 0 := by
    intro α' hα
    exact A₂ _ fun hc => hα (Finset.mem_union_right _ hc)
  refine ⟨z₁, z₂, ?_⟩

  have E₁ : ∑ α' ∈ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val =
      ∑ α ∈ S₁, sval (f α) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t α) r z J).val := by
    rw [← Finset.sum_subset (Finset.subset_union_left) (fun α' _ hα => by
      rw [A₁ (xe α') fun hc => hα (Finset.mem_map.2 ⟨xe α', hc, xe.symm_apply_apply α'⟩), zero_mul]),
      Finset.sum_map]
    refine Finset.sum_congr rfl fun α _ => ?_
    have h₀ : xe (xe.symm.toEquiv.toEmbedding α) = α := xe.apply_symm_apply α
    rw [h₀]
  have E₂ : ∑ α' ∈ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val =
      ∑ α' ∈ S₂, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val :=
    (Finset.sum_subset (Finset.subset_union_right) (fun α' _ hα => by rw [A₂ α' hα, zero_mul])).symm
  rw [E₁, E₂]
  obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((fstG (maximalIdeal R) e G).left (r z))
  obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG (maximalIdeal R) e G).left (r z))
  rw [← B₁ jL hL, ← B₂ jL' hL']
  obtain ⟨J₀, hJ₀, k₀⟩ := exists_good U.LG.L U.LG.isLB z (fun _ : PUnit => r ≫ (fstG (maximalIdeal R) e G).left)
    (fun _ => jL) (fun _ _ _ => rfl) (fun _ => hL)
  obtain ⟨J₀', hJ₀', k₀'⟩ := exists_good U'.LG.L U'.LG.isLB z (fun _ : PUnit => r ≫ (fstG (maximalIdeal R) e G).left)
    (fun _ => jL') (fun _ _ _ => rfl) (fun _ => hL')
  have c₀ : J₀ (r ≫ (fstG (maximalIdeal R) e G).left) = jL := k₀ PUnit.unit
  have c₀' : J₀' (r ≫ (fstG (maximalIdeal R) e G).left) = jL' := k₀' PUnit.unit
  have hS : sv U.toUnifPre 2 σ (r ≫ (fstG (maximalIdeal R) e G).left) z jL =
      (gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')).val *
        sv U'.toUnifPre 2 σ' (r ≫ (fstG (maximalIdeal R) e G).left) z jL' := by
    have H := hσ Z (r ≫ (fstG (maximalIdeal R) e G).left) z J₀ J₀' hJ₀ hJ₀'
    rw [sval_of σ _ z J₀ (fun _ => jL) (fun _ => by rw [Category.comp_id]; exact c₀),
      sval_of σ' _ z J₀' (fun _ => jL') (fun _ => by rw [Category.comp_id]; exact c₀'), c₀, c₀'] at H
    exact H
  have W : gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) *
        wv U'.toUnifPre e r z (J' (r ≫ (U'.gt e).pG.left)) jL' ^ 2 =
      wv U.toUnifPre e r z (J (r ≫ (U.gt e).pG.left)) jL ^ 2 *
        gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') :=
    (hlev e).2 Z r z (J (r ≫ (U.gt e).pG.left)) (J' (r ≫ (U'.gt e).pG.left)) jL jL' (hJ _) (hJ' _) hL hL'
  have hO : ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left) =
      gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) := by
    show gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J ((r ≫ (U'.gt e).pG.left) ≫ Φ.hom.left))
      (fun _ => J' (r ≫ (U'.gt e).pG.left)) = _
    rw [Category.assoc, (hlev e).1]
  rw [hS, hO, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, W]

end GlobalTheory
end

