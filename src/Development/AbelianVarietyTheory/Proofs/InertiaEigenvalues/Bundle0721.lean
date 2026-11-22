import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0047
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0627
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0704
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0711
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TranslateSumVacuumMovedByAdelicPair

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergEpsilonTransport
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PairEpsTransport

section Maps
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)

theorem map_longElt (n : ℕ) : GeneralLinearGroup.map f (longElt n R) = longElt n S := by
  ext i j; simp [longElt, GeneralLinearGroup.map]

theorem map_invT (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (GlobalTheory.CuspRep.invT n R g) = GlobalTheory.CuspRep.invT n S (GeneralLinearGroup.map f g) := by
  ext i j
  have h := congrArg (fun h : GL (Fin n) S => (h : Matrix (Fin n) (Fin n) S) j i)
    (map_inv (GeneralLinearGroup.map f) g)
  exact h

theorem map_tilde {n : ℕ} (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (tilde g) = tilde (GeneralLinearGroup.map f g) := by
  rw [tilde, tilde, map_mul, map_longElt, map_invT]

theorem map_corner {m : ℕ} (g : GL (Fin m) R) :
    GeneralLinearGroup.map f (corner g) = corner (GeneralLinearGroup.map f g) := by
  ext i j
  show f ((emb₂ R (stdSum (rfl : m + 1 = m + 1)) (g, 1) : Matrix _ _ R) i j) =
    (emb₂ S (stdSum (rfl : m + 1 = m + 1)) (GeneralLinearGroup.map f g, 1) : Matrix _ _ S) i j
  rw [val_emb₂, val_emb₂]
  obtain ⟨i, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective i
  obtain ⟨j, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, GeneralLinearGroup.map] <;> split_ifs <;> simp

theorem superDiag_map {n : ℕ} (g : GL (Fin n) R) :
    GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map f g) = f (GlobalTheory.Whittaker.superDiag g) := by
  simp [GlobalTheory.Whittaker.superDiag, map_sum, GeneralLinearGroup.map]

theorem map_mem_unipB {n : ℕ} {g : GL (Fin n) R} (hg : g ∈ unipB R (Fin n)) :
    GeneralLinearGroup.map f g ∈ unipB S (Fin n) := by
  rw [mem_unipB] at hg ⊢
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp [GeneralLinearGroup.map, hg.1 i j h]
  · simp [GeneralLinearGroup.map, hg.2 i]

end Maps

section Core

variable {k k' : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
  [Field k'] [TopologicalSpace k'] [IsTopologicalRing k']

theorem map_map_symm {n : ℕ} (i : k ≃+* k') (g : GL (Fin n) k') :
    GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g := by
  ext a b; simp [GeneralLinearGroup.map]

theorem map_symm_map {n : ℕ} (i : k ≃+* k') (g : GL (Fin n) k) :
    GeneralLinearGroup.map i.symm.toRingHom (GeneralLinearGroup.map i.toRingHom g) = g := by
  ext a b; simp [GeneralLinearGroup.map]

theorem continuous_mapGL {n : ℕ} (i : k ≃+* k') (hi : Continuous i) :
    Continuous (GeneralLinearGroup.map (n := Fin n) i.toRingHom) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hi
  · exact Units.continuous_coe_inv.matrix_map hi

end Core

section Transport

variable {k k' : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
  [Field k'] [TopologicalSpace k'] [IsTopologicalRing k']

theorem isTestFun_comp {m : ℕ} (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm)
    {f : GL (Fin m) k → ℂ} (hf : IsTestFun f) :
    IsTestFun (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g)) := by
  obtain ⟨h1, h2, C, hC, h3⟩ := hf
  refine ⟨fun u hu g => ?_, h2.comp_continuous (continuous_mapGL i.symm hi'), ?_⟩
  · show f (GeneralLinearGroup.map i.symm.toRingHom (u * g)) = f (GeneralLinearGroup.map i.symm.toRingHom g)
    rw [map_mul]
    exact h1 _ (map_mem_unipB _ hu) _
  · refine ⟨GeneralLinearGroup.map i.toRingHom '' C, hC.image (continuous_mapGL i hi), fun g hg => ?_⟩
    obtain ⟨u, hu, c, hc, he⟩ := h3 _ hg
    refine ⟨GeneralLinearGroup.map i.toRingHom u, map_mem_unipB _ hu, GeneralLinearGroup.map i.toRingHom c,
      ⟨c, hc, rfl⟩, ?_⟩
    rw [← map_mul, ← he, map_map_symm]

variable {m : ℕ} {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem hasPairEps_of_equiv (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm)
    {ψ : AddChar k Circle} {ψ' : AddChar k' Circle} (hψ : ∀ x, ψ' (i x) = ψ x)
    {π : Representation ℂ (GL (Fin (m + 1)) k) V} {π' : Representation ℂ (GL (Fin (m + 1)) k') V'}
    {τ : Representation ℂ (GL (Fin m) k) W} {τ' : Representation ℂ (GL (Fin m) k') W'}
    (A : V ≃ₗ[ℂ] V') (hA : ∀ g v, A (π g v) = π' (GeneralLinearGroup.map i.toRingHom g) (A v))
    (B : W ≃ₗ[ℂ] W') (hB : ∀ g v, B (τ g v) = τ' (GeneralLinearGroup.map i.toRingHom g) (B v))
    {c : ℂ} (H : HasPairEps ψ π τ c) : HasPairEps ψ' π' τ' c := by
  intro ω' hω' l' L' hl' hL' I' hI' v' w'
  have hψinv : ∀ x, (ψ'⁻¹) (i x) = (ψ⁻¹) x := by
    intro x; simp only [AddChar.inv_apply]; rw [← map_neg, hψ]
  have hω : HasCentralChar τ (ω'.comp (Units.map i.toRingHom.toMonoidHom)) := by
    intro z w
    apply B.injective
    rw [hB, GeneralLinearGroup.map_scalar, hω', map_smul]
    rfl
  have hl : GlobalTheory.Whittaker.IsFunctional ψ π (l'.comp A.toLinearMap) := by
    intro u hu v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hA, hl' _ (map_mem_unipB _ hu), superDiag_map]
    simp [hψ]
  have hL : GlobalTheory.Whittaker.IsFunctional ψ⁻¹ τ (L'.comp B.toLinearMap) := by
    intro u hu v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hB, hL' _ (map_mem_unipB _ hu), superDiag_map]
    have := hψinv (GlobalTheory.Whittaker.superDiag u)
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [this]
  have hI : IsInvIntegral (I'.comp (LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n := Fin m) i.symm.toRingHom))) := by
    intro f hf x
    change I' (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g * x)) =
      I' (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g))
    have := hI' _ (isTestFun_comp i hi hi' hf) (GeneralLinearGroup.map i.toRingHom x)
    refine Eq.trans ?_ this
    congr 1
    funext g
    rw [map_mul, map_symm_map]
  have key := H _ hω _ _ hl hL _ hI (A.symm v') (B.symm w')
  have e1 : LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n := Fin m) i.symm.toRingHom)
      (fun g => (l'.comp A.toLinearMap) (π (tilde (corner g)) (A.symm v')) *
        (L'.comp B.toLinearMap) (τ (tilde g) (B.symm w'))) =
      fun g => l' (π' (tilde (corner g)) v') * L' (τ' (tilde g) w') := by
    funext g
    simp only [LinearMap.funLeft_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Function.comp_apply, hA, hB,
      map_tilde, map_corner, map_map_symm, LinearEquiv.apply_symm_apply]
  have e2 : LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n := Fin m) i.symm.toRingHom)
      (fun g => (l'.comp A.toLinearMap) (π (corner g) (A.symm v')) *
        (L'.comp B.toLinearMap) (τ g (B.symm w'))) =
      fun g => l' (π' (corner g) v') * L' (τ' g w') := by
    funext g
    simp only [LinearMap.funLeft_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Function.comp_apply, hA, hB,
      map_corner, map_map_symm, LinearEquiv.apply_symm_apply]
  have e3 : (ω'.comp (Units.map i.toRingHom.toMonoidHom)) (-1) = ω' (-1) := by
    simp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, e2, e3] at key
  exact key
end Transport

section Main

theorem equiv_apply_rep {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (g : G) (v : V) :
    φ.toLinearEquiv (ρ g v) = σ g (φ.toLinearEquiv v) :=
  LinearMap.congr_fun (φ.toIntertwiningMap.isIntertwining' g) v

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem exists_equiv_of_repRel (i : k ≃+* k') {n : ℕ} {π : IrrRep (GL (Fin n) k)} {π' : IrrRep (GL (Fin n) k')}
    (h : RepRel i (cls π) (cls π')) :
    ∃ E : π.V ≃ₗ[ℂ] π'.V, ∀ g v, E (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (E v) := by
  obtain ⟨n₀, π₀, π₀', e, h1, h2, he⟩ := h
  obtain ⟨rfl, h1⟩ := Sigma.mk.inj_iff.1 h1
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.1 h2
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 (eq_of_heq h1)
  obtain ⟨φ'⟩ := IrrRep.cl_eq_iff.1 (eq_of_heq h2)
  refine ⟨φ.toLinearEquiv ≪≫ₗ e ≪≫ₗ φ'.toLinearEquiv.symm, fun g v => ?_⟩
  apply φ'.toLinearEquiv.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [equiv_apply_rep φ, he, equiv_apply_rep φ', LinearEquiv.apply_symm_apply]

end Main

end GlobalTheory.PairEpsTransport

open GlobalTheory.PairEpsTransport in

theorem GlobalTheory.LocLanglands.hasPairEps_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle), (∀ x, ψ' (i x) = ψ x) → ∀ (m : ℕ) (π : IrrRep (GL (Fin (m + 1)) k)) (π' : IrrRep (GL (Fin (m + 1)) k')) (τ : IrrRep (GL (Fin m) k)) (τ' : IrrRep (GL (Fin m) k')) (c : ℂ), RepRel i (cls π) (cls π') → RepRel i (cls τ) (cls τ') → HasPairEps ψ π.ρ τ.ρ c → HasPairEps ψ' π'.ρ τ'.ρ c := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi ψ ψ' hψ m π π' τ τ' c hπ hτ H
  have hi' : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi).1
  obtain ⟨A, hA⟩ := exists_equiv_of_repRel i hπ
  obtain ⟨B, hB⟩ := exists_equiv_of_repRel i hτ
  exact hasPairEps_of_equiv i hi hi' hψ A hA B hB H

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparableCompSmul
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open Formalism.IndefR.NX
open scoped TensorProduct

namespace GlobalTheory.GoodSS

theorem aeval_intertwine {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (e : M ≃ₗ[K] N) (A : Module.End K M) (B : Module.End K N) (h : ∀ x, e (A x) = B (e x)) (p : K[X]) (x : M) :
    e (Polynomial.aeval A p x) = Polynomial.aeval B p (e x) := by
  have hpow : ∀ n : ℕ, ∀ x, e ((A ^ n) x) = (B ^ n) (e x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a => simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow]

theorem separable_comp_smul {K : Type} [Field K] {p : K[X]} (hp : p.Separable) {a : K} (ha : a ≠ 0) :
    (p.comp (Polynomial.C a * Polynomial.X)).Separable := by
  have h1 := IsCoprime.map hp (Polynomial.compRingHom (Polynomial.C a * Polynomial.X))
  rw [Polynomial.coe_compRingHom_apply, Polynomial.coe_compRingHom_apply] at h1
  have h2 : IsCoprime (p.comp (Polynomial.C a * Polynomial.X)) (Polynomial.C a) :=
    ⟨0, Polynomial.C a⁻¹, by rw [zero_mul, zero_add, ← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1]⟩
  have h3 : Polynomial.derivative (p.comp (Polynomial.C a * Polynomial.X)) =
      (Polynomial.derivative p).comp (Polynomial.C a * Polynomial.X) * Polynomial.C a := by
    rw [Polynomial.derivative_comp, Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
      zero_mul, zero_add, mul_one, mul_comm]
  show IsCoprime _ _
  rw [h3]
  exact h1.mul_right h2

theorem aeval_smul_comp {K M : Type} [Field K] [AddCommGroup M] [Module K M] (B : Module.End K M) {c : K}
    (hc : c ≠ 0) (p : K[X]) (y : M) :
    Polynomial.aeval (c • B) (p.comp (Polynomial.C c⁻¹ * Polynomial.X)) y = Polynomial.aeval B p y := by
  rw [Polynomial.aeval_comp]
  congr 2
  rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

set_option maxHeartbeats 800000 in

theorem hkF_separable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y) : CommG D → HkComm D → NExpHeckeRowX Rl cG S Y H (fun j => goodProjW S j D.nexp.eLL0) →
    Rl.Char3 F → Rl.toRealDat.LUnif → Rl.toRealDat.LIntegral →
    (∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i) →
    (∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host))) →
    (∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i) →
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
      ∃ p : (FractionRing (D.ntw.O i))[X], p.Separable ∧
        ∀ x ∈ V0 D.nexp i j b, Polynomial.aeval (D.nexp.hkF i j b k P) p x = 0 := by
  intro hG hC hX hR hU hI hS0c hS02 hS0b i hi j hj b k P hk
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨q, hqs, hq⟩ := GlobalTheory.T.hecke_commutation_real_expansion Rl F cG S Y H hG hC hX hR hU hI hS0c hS02 hS0b i hi j h1 h2 b k P hk

  set rd : ↥D.LL0 →+* KB S i b := readLL0 S i b with hrd
  set hst := Y.rho j h1 h2
  set hχ := Y.chi j h1 h2
  set T0 := GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) with hT0
  set s := (D.nexp.eAlg i b).coeff.support with hs
  set a : G0g D.nd → ↥D.LL0 := fun g => D.nexp.eLL0 g * (chiL S j hχ (S.eG.symm g))⁻¹ with ha
  set ρ : G0g D.nd → Module.End S.Ks (FmK S j) := fun g => rhoKG S j hst (S.eG.symm g) with hρ

  have hcoef : ∀ g, (D.nexp.eAlg i b).coeff g = rd (D.nexp.eLL0 g) := fun g => by
    rw [D.nexp.eAlg_def]; rfl
  have hsupp : ∀ g, g ∉ s → D.nexp.eLL0 g = 0 := fun g hg => by
    have h0 : (D.nexp.eAlg i b).coeff g = 0 := Finsupp.notMem_support_iff.1 hg
    rw [hcoef] at h0
    exact (map_eq_zero_iff rd rd.injective).1 h0

  have hE' : GlobalTheory.GoodSS.goodProjectorBaseChangeForms S j hst hχ D.nexp.eLL0 = ∑ g ∈ s, a g • LinearMap.baseChange ↥D.LL0 (ρ g) := by
    unfold GlobalTheory.GoodSS.goodProjectorBaseChangeForms
    refine finsum_eq_sum_of_support_subset _ fun g hg => ?_
    by_contra hgs
    exact hg (by simp only [hsupp g hgs, zero_mul, zero_smul])

  have hdesc := GlobalTheory.T.baseChange_polynomial_annihilates_descent S.Ks ↥D.LL0 (KB S i b) (FmK S j) (G0g D.nd) rd (fun _ => rfl) T0 s ρ a q
    (fun z hz => hq z (hE' ▸ hz))
  set c := H.cHk i b k P with hc
  have hc0 : c ≠ 0 := by
    rw [hc, H.cHk_pow]
    exact pow_ne_zero _ (H.cHk_unit i b P).ne_zero

  set B : Module.End (FractionRing (D.ntw.O i)) (Fm S i j b) := LinearMap.baseChange (KB S i b) T0 with hB
  have hAB : ∀ x, Y.eF i j b h1 h2 (D.nexp.hkF i j b k P x) = (c • B) (Y.eF i j b h1 h2 x) := fun x =>
    H.hkEq i j b h1 h2 k P x hk.2.2.2 hk.2.2.1 hk.2.1

  have hE : ∀ x0, Y.eF i j b h1 h2 (eG D.nexp i j b x0) =
      (∑ g ∈ s, rd (a g) • LinearMap.baseChange (KB S i b) (ρ g)) (Y.eF i j b h1 h2 x0) := by
    intro x0
    have hact : ∀ g y, actG S i j b hst hχ g y =
        (rd (chiL S j hχ (S.eG.symm g)))⁻¹ • LinearMap.baseChange (KB S i b) (ρ g) y := fun _ _ => rfl
    rw [eG, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply, map_sum]
    refine (Finset.sum_congr rfl fun g _ => ?_).trans (LinearMap.sum_apply _ _ _).symm
    change Y.eF i j b h1 h2 ((D.nexp.eAlg i b).coeff g • D.nexp.actG i j b g x0) =
      rd (a g) • LinearMap.baseChange (KB S i b) (ρ g) (Y.eF i j b h1 h2 x0)
    rw [map_smul, Y.act i j b h1 h2 g x0, hact, hcoef]
    have hag : rd (a g) = rd (D.nexp.eLL0 g) * (rd (chiL S j hχ (S.eG.symm g)))⁻¹ := by
      simp only [ha, map_mul, map_inv₀]
    rw [hag]
    exact (mul_smul _ _ _).symm
  refine ⟨(q.map rd).comp (Polynomial.C c⁻¹ * Polynomial.X), ?_, ?_⟩
  · exact separable_comp_smul ((Polynomial.separable_map rd).2 hqs) (inv_ne_zero hc0)
  · rintro x ⟨x0, -, rfl⟩
    apply (Y.eF i j b h1 h2).injective
    rw [map_zero]
    refine (aeval_intertwine (Y.eF i j b h1 h2) _ (c • B) hAB _ _).trans ?_
    refine (aeval_smul_comp B hc0 _ _).trans ?_
    rw [hE]
    exact hdesc _ ⟨_, rfl⟩

end GlobalTheory.GoodSS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideRealMoreLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SideLevel
open Formalism.IndefR.Lev

theorem surj_restrict {A G : Type} [Group A] [Group G] {J Q Q' : Subgroup A} (h : Q' ≤ Q) (red : Q →* G)
    (hs : Function.Surjective red) (hk : ∀ q : Q, red q = 1 ↔ (q : A) ∈ J)
    (hm : ∀ g ∈ Q, ∃ g' ∈ Q', g⁻¹ * g' ∈ J) : Function.Surjective (red.comp (Subgroup.inclusion h)) := by
  intro g
  obtain ⟨q, rfl⟩ := hs g
  obtain ⟨g', hg', hJ⟩ := hm q q.2
  refine ⟨⟨g', hg'⟩, ?_⟩
  have h1 : red (q⁻¹ * ⟨g', h hg'⟩) = 1 := (hk _).2 hJ
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

set_option maxHeartbeats 3200000 in

theorem sideReal_moreLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok ok' : Set Pl0) (Sp : Set (Pl D.host.E)), L.Q ⊆ Q' → ok' ⊆ ok → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → (∀ P ∈ ok', Bridge.SplitOff (pl P) Sp) → (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ∈ Sp) → (∀ j, j < L.s → ∀ PP ∈ L.Pg, ∀ x, ∃ a, D.what₂.embLL a = ((L.cg (j + 1) PP x : ℂˣ) : ℂ)) → (∀ PP ∈ Q', ∀ x, ∃ a, D.what₂.embLL a = ((xq PP x : ℂˣ) : ℂ)) → ∀ (c : Bridge.CoefDat D V) (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G S.Forms) (op : ok × ℕ → Module.End D.what₂.LL S.Forms) (B : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β L pl ok)) S act op (fun i => i.2)), (∃ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (rho : _) (pair : _) (nab del : _), Bridge.CoefMapTie V c c0 rho ∧ Bridge.CoefTie V c B.pres lam c0 pair nab del) → ∃ (S' : CSD D.what₂.LL) (act' : Representation D.what₂.LL G S'.Forms) (op' : ok' × ℕ → Module.End D.what₂.LL S'.Forms) (B' : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β { L with Q := Q', xq := xq } pl ok')) S' act' op' (fun i => i.2)), (∀ q : (levEnv V β { L with Q := Q', xq := xq }).Q, ∃ hq : (q : Bridge.Gf V) ∈ (levEnv V β L).Q, B'.act_tie.red q = B.act_tie.red ⟨q, hq⟩) ∧ (∀ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair nab del, Bridge.CoefTie V c B.pres lam c0 pair nab del → Bridge.CoefTie V c B'.pres lam c0 pair nab del) ∧ ∀ P, op' (P, 0) = 1 ∧ ∀ k, V.rank < k → op' (P, k) = 0 := by
  intro D G _ _ V β Λ hSD L Q' xq Pl0 pl ok ok' Sp hQ hok hdisj hsplit hS hcg hxq c S act op B hct
  have hfin := GlobalTheory.T.parahoricSublevel_finiteIndex_more_places D V β Λ hSD L Q' xq hQ
  obtain ⟨hJle, hQle, hfi, hker⟩ := hfin
  obtain ⟨cc, hβ⟩ := hSD
  rw [one_pow] at hβ
  have hSD' : IsSDFrame V β Λ 1 := ⟨cc, by rw [one_pow]; exact hβ⟩
  let L' : LevDat D.host.E ℂ V.rank := { L with Q := Q', xq := xq }
  have hval : ∀ q : (levEnv V β L').Q, ∃ a, D.what₂.embLL a = (((levEnv V β L').ch q : ℂˣ) : ℂ) :=
    fun q => GlobalTheory.TwistCharChange.flag_vals V β L' hcg hxq _
  have hvalJ : ∀ k : (levEnv V β L').J, ∃ a, D.what₂.embLL a = (((levEnv V β L').χ k : ℂˣ) : ℂ) := by
    intro k
    rw [← (levEnv V β L').ch_J k]
    exact hval _
  have hrat : ∀ (γ : GQ V) x, ∃ x', B.pres.coef x' = c.ρ γ (B.pres.coef x) := by
    obtain ⟨lam, c0, rho, pair, nab, del, hmap, e, -, hco, -⟩ := hct
    intro γ x
    obtain ⟨γE, hγ⟩ := GlobalTheory.TwistCharChange.ratMat_exists V γ
    refine ⟨e.symm (rho γE (e x)), ?_⟩
    refine ((hco _).trans ?_).trans (congrArg (c.ρ γ) (hco x)).symm
    rw [LinearEquiv.apply_symm_apply]
    exact hmap.1 γ γE hγ (e x)
  obtain ⟨Cl, fC, π, kc, Gam, gG, fG, ρ', P', hy, hcoef⟩ := GlobalTheory.T.classPres_of_finiteIndex_subLevel (Bridge.ratF V) D.what₂.embLL S c.ρ
    (levEnv V β L).J (levEnv V β L).χ B.pres (levEnv V β L').J hJle hfi (levEnv V β L').χ hvalJ hrat
  have hrat' : ∀ (γ : GQ V) x, ∃ x', P'.coef x' = c.ρ γ (P'.coef x) := by
    rw [hcoef]; exact hrat

  let red' : (levEnv V β L').Q →* G := B.act_tie.red.comp (Subgroup.inclusion hQle)
  have hred_surj : Function.Surjective red' :=
    surj_restrict hQle B.act_tie.red B.act_tie.red_surj B.act_tie.red_ker (GlobalTheory.T.exists_mem_smaller_parahoricLevel_mod_firstBlocks D V β Λ hSD' L Q' xq hQ hdisj)
  have hred_ker : ∀ q : (levEnv V β L').Q, red' q = 1 ↔ (q : Bridge.Gf V) ∈ (levEnv V β L').J := by
    intro q
    exact (B.act_tie.red_ker ⟨q, hQle q.2⟩).trans ⟨fun h => hker _ q.2 h, fun h => hJle h⟩

  let up : ok' × ℕ → ok × ℕ := fun i => (⟨i.1, hok i.1.2⟩, i.2)
  have hoffI : ∀ i : ok' × ℕ, ∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1) :=
    fun i PP h => GlobalTheory.SplitHeckeAdj.off_of_splitOff (hsplit i.1.1 i.1.2) PP (hS PP h)
  have hHk : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → isTEnv V pl ok' i (B.hecke.hx (up i)) ∧
      (∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok' i a) ∧ Bridge.IsDC (levEnv V β L').J (B.hecke.hx (up i)) (B.hecke.hA (up i)) := by
    intro i hi
    have hT : isTEnv V pl ok (up i) (B.hecke.hx (up i)) := B.hecke.hx_ok (up i) hi
    have hA : ∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok (up i) a := B.hecke.hA_loc (up i) hi
    refine ⟨hT, hA, ?_⟩
    exact GlobalTheory.T.hecke_representatives_split_place_smaller_level D V β Λ hSD' L Q' xq hQ Pl0 pl ok (up i) (hoffI i) hi.2 _ _ hT hA (B.hecke.hDC (up i) hi)
  have hloc : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → ∃ Lc : Subgroup (Bridge.Gf V),
      (∀ x, isLocEnv V pl ok' i x → x ∈ Lc) ∧
      (∀ k ∈ (levEnv V β L').J, ∃ k₁ ∈ (levEnv V β L').J, ∃ k₂ ∈ (levEnv V β L').J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧
        ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : (levEnv V β L').J, (k : Bridge.Gf V) ∈ Lc → (levEnv V β L').χ k = 1 := by
    intro i hi
    obtain ⟨α, hα, -⟩ := B.hecke.hx_ok (up i) hi hi.2
    obtain ⟨e, -, he, -⟩ := hα
    obtain ⟨Lc, l1, l2, l3, -⟩ := GlobalTheory.SplitHeckeAdj.local_group V β Λ L' hβ (pl i.1) e he (hoffI i)
    refine ⟨Lc, fun x hx => ?_, l2, l3⟩
    obtain ⟨g, hg, rfl⟩ := GlobalTheory.SplitHeckeAdj.loc_supp V hx he
    exact l1 g hg
  obtain ⟨act', op', B', hpres, hred, hop⟩ := GlobalTheory.T.classPres_forms_finiteGroup_heckeOperators (Bridge.ratF V) c (levEnv V β L') (isTEnv V pl ok')
    (isLocEnv V pl ok') D.what₂.embLL _ (fun i : ok' × ℕ => 1 ≤ i.2 ∧ i.2 ≤ V.rank) P' hval hrat' red' hred_surj hred_ker
    (fun i => B.hecke.hx (up i)) (fun i => B.hecke.hA (up i)) hHk hloc (fun i => i.2 = 0)
  subst hpres
  have hl : ∀ cl, Bridge.hLat V (B'.pres.y cl) = Bridge.hLat V (B.pres.y (π cl)) := fun cl =>
    (congrArg (Bridge.hLat V) (hy cl)).trans (GlobalTheory.T.hermitian_lattice_invariant_under_level D V β Λ hSD' L _ _ (kc cl).2)
  refine ⟨_, act', op', B', fun q => ⟨hQle q.2, DFunLike.congr_fun hred q⟩, ?_, ?_⟩
  · rintro lam c0 pair nab del ⟨e, h1, h2, h3, h4, h5⟩
    exact ⟨e, h1, fun x => (DFunLike.congr_fun hcoef x).trans (h2 x), h3,
      fun cl => (h4 (π cl)).trans (congrArg nab (hl cl).symm), fun cl => (h5 (π cl)).trans (congrArg del (hl cl).symm)⟩
  · intro P
    refine ⟨(hop (P, 0) (by simp)).1 rfl, fun k hk => (hop (P, k) (by simp only [not_and, not_le]; intro; omega)).2 (by simp only; omega)⟩

end GlobalTheory.SideLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilSumDoubleIntegralExchangeCuspFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilSum_doubleIntegral_exchange_cuspForms : ∀ D : D7, EisAbs D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ Y : Lag W, IntegrableOn (fun p : GA D W × GA D W => star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) (𝓖 ×ˢ 𝓖) (νW.prod νW)) ∧ Summable (fun Y : Lag W => ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW)) ∧ ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∑' Y : Lag W, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  first | exact @GlobalTheory.RallisExch.eisAbs_exchange | exact GlobalTheory.RallisExch.eisAbs_exchange | (intros; apply GlobalTheory.RallisExch.eisAbs_exchange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardModulePropertiesStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_module_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.LanglandsMultisegments →
    ∀ (P : Segment k → Prop), (∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, P Δ) → ∃ y : IrrGL k, IsL 𝔫 y.rep) →
    ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (𝔪 : Fin h → Multiset (Segment k)),
      (∀ j, IsL (𝔪 j) (x j).rep) → (∀ j, ∀ Δ ∈ 𝔪 j, P Δ) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible →
        Nonempty (π.Equiv (prodIrr x hd)) → IsL (∑ j, 𝔪 j) π := by
  first | exact @GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible | exact GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible | (intros; apply GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TranslateSumVacuumMovedByAdelicPairStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translateSum_vacuum_moved_by_adelicPair : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW s f₀ → ∀ (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → ∀ (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ (r : ℕ) (hr : W.rank = r) (bad N : ℕ) (h : GA D V) (k : GA D W) (Λ : GenLat D.host.E V.rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), l₂.M ∣ bad → SplitOffBad V bad h → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (finPt V h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ W hr ι k mk → ∀ (Y : (Fin V.rank → LevQ Dw l₂) → Matrix (Fin V.rank) (Fin r) D.host.E) (γ : (Fin V.rank → LevQ Dw l₂) → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : (Fin V.rank → LevQ Dw l₂) → WO V W), IsRoots l₂ (latR hr (latG W k)) mk N Y → (∀ q, colsR hr (γ q) = Y q ∧ IsFinOf V W (γ q) (u q)) → ∀ w : (Fin V.rank → LevQ Dw l₂) → ℂ, IsThetaFunO ψ V W (transSum ψ V W l₂ ι e f₀ w) ∧ om (h, k) (transSum ψ V W l₂ ι e f₀ w) = ((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin V.rank → LevQ Dw l₂, w q • heisO ψ V W (u q) (om (h, k) f₀) := by
  first | exact @GlobalTheory.AdTh.MovedSum.moved_transSum | exact GlobalTheory.AdTh.MovedSum.moved_transSum | (intros; apply GlobalTheory.AdTh.MovedSum.moved_transSum <;> assumption)
end

