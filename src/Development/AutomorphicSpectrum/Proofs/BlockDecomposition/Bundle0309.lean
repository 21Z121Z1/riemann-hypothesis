import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0022
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingOperatorsKernelLift
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem exists_grSum_semilift {ι : Type} {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
    {N : Type} [AddCommGroup N] [Module (MvPolynomial ι R') N] (φ : ∀ n, A n →+ N)
    (hr : ∀ n (r : R) (a : A n),
      φ n (r • a) = (MvPolynomial.C (f r) : MvPolynomial ι R') • φ n a)
    (hX : ∀ i n (a : A n),
      φ (n + 1) (x i n a) = (MvPolynomial.X i : MvPolynomial ι R') • φ n a) :
    ∃ Φ : GrSum hx →+ N, (∀ n a, Φ (GrSum.of hx n a) = φ n a) ∧
      ∀ (q : MvPolynomial ι R) (u : GrSum hx), Φ (q • u) = (MvPolynomial.map f q) • Φ u := by
  letI : Module R N := Module.compHom N ((MvPolynomial.C : R' →+* MvPolynomial ι R').comp f)
  letI : Module (MvPolynomial ι R) N :=
    Module.compHom N (MvPolynomial.map f : MvPolynomial ι R →+* MvPolynomial ι R')
  haveI : IsScalarTower R (MvPolynomial ι R) N := ⟨fun r q m => by
    change (MvPolynomial.map f (r • q)) • m =
      (MvPolynomial.C (f r) : MvPolynomial ι R') • (MvPolynomial.map f q) • m
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, mul_smul]⟩
  let ψ : ∀ n, A n →ₗ[R] N := fun n =>
    { toFun := φ n, map_add' := map_add _, map_smul' := fun r a => hr n r a }
  have hψ : ∀ i n a, ψ (n + 1) (x i n a) = (MvPolynomial.X i : MvPolynomial ι R) • ψ n a := by
    intro i n a
    change φ (n + 1) (x i n a) = (MvPolynomial.map f (MvPolynomial.X i)) • φ n a
    rw [MvPolynomial.map_X]
    exact hX i n a
  refine ⟨(GrSum.lift hx ψ hψ).toAddMonoidHom, fun n a => GrSum.lift_of hx ψ hψ n a,
    fun q u => ?_⟩
  exact (GrSum.lift hx ψ hψ).map_smul q u

section Tower

variable {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ} {ρ : Fin g → R}
  {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)]
  {res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S'}
  {p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S}
  {mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S}

theorem smul_mem_Ks (H : TowerAx ρ res p mm) {e : ℕ} {t : ℤ} {S : Finset ι} (hS : S.Nonempty)
    {r : R} (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (y : T (e + 1) t S) :
    r • y ∈ Ks p e t S := by
  rw [mem_Ks hS, map_smul]
  exact H.smul_eq_zero_of_mem hS (m := e + 1) (n := 0) (by omega) hr (by simp)

variable (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S)
  fun j t => mm j e t S)

theorem exists_mulMap (H : TowerAx ρ res p mm) {e : ℕ} {r : R}
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) {S : Finset ι} (hS : S.Nonempty) :
    ∃ Φ : GrSum (hc (e + 1) S) →+ H.Tot hc S,
      (∀ t y, Φ (GrSum.of (hc (e + 1) S) t y) =
        (H.ops hc S).of e t ⟨r • y, smul_mem_Ks H hS hr y⟩) ∧
      ∀ (q : MvPolynomial ι R) (u : GrSum (hc (e + 1) S)),
        Φ (q • u) = (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial (Fin g) R) q) • Φ u := by
  let μ : ∀ t, T (e + 1) t S →+ Ks p e t S := fun t =>
    { toFun := fun y => ⟨r • y, smul_mem_Ks H hS hr y⟩
      map_zero' := Subtype.ext (smul_zero r)
      map_add' := fun a b => Subtype.ext (smul_add r a b) }
  obtain ⟨Φ, h1, h2⟩ := exists_grSum_semilift (MvPolynomial.C : R →+* MvPolynomial (Fin g) R)
    (hc (e + 1) S) (N := H.Tot hc S) (fun t => ((H.ops hc S).of e t).comp (μ t))
    (fun t c a => by
      simp only [AddMonoidHom.comp_apply]
      rw [BiOps.C_C_smul_of]
      congr 1
      exact Subtype.ext (smul_comm r c a))
    (fun j t a => by
      simp only [AddMonoidHom.comp_apply]
      rw [BiOps.X_smul_of]
      congr 1
      apply Subtype.ext
      change r • mm j (e + 1) t S a = mm j (e + 1) t S (r • a)
      rw [map_smul])
  exact ⟨Φ, h1, h2⟩

def unitIdeal (H : TowerAx ρ res p mm) (one : ∀ e (i : ι), T e 0 {i}) (i : ι)
    (Q : Submodule (MvPolynomial ι (MvPolynomial (Fin g) R)) (H.Tot hc {i})) (e : ℕ) : Ideal R where
  carrier := {r | ∃ h : r • one (e + 1) i ∈ Ks p e 0 {i},
    (H.ops hc {i}).of e 0 ⟨r • one (e + 1) i, h⟩ ∈ Q}
  add_mem' := by
    rintro a b ⟨ha, ma⟩ ⟨hb, mb⟩
    have h : (a + b) • one (e + 1) i ∈ Ks p e 0 {i} := by
      rw [add_smul]
      exact add_mem ha hb
    refine ⟨h, ?_⟩
    have e1 : (⟨(a + b) • one (e + 1) i, h⟩ : Ks p e 0 {i}) =
        ⟨a • one (e + 1) i, ha⟩ + ⟨b • one (e + 1) i, hb⟩ := Subtype.ext (add_smul a b _)
    rw [e1, map_add]
    exact add_mem ma mb
  zero_mem' := by
    have h : (0 : R) • one (e + 1) i ∈ Ks p e 0 {i} := by
      rw [zero_smul]
      exact zero_mem _
    refine ⟨h, ?_⟩
    have e1 : (⟨(0 : R) • one (e + 1) i, h⟩ : Ks p e 0 {i}) = 0 := Subtype.ext (zero_smul R _)
    rw [e1, map_zero]
    exact zero_mem _
  smul_mem' := by
    rintro c a ⟨ha, ma⟩
    have h : (c • a) • one (e + 1) i ∈ Ks p e 0 {i} := by
      rw [smul_assoc]
      exact Submodule.smul_mem _ c ha
    refine ⟨h, ?_⟩
    have e1 : (⟨(c • a) • one (e + 1) i, h⟩ : Ks p e 0 {i}) =
        c • ⟨a • one (e + 1) i, ha⟩ := Subtype.ext (smul_assoc c a _)
    rw [e1, ← BiOps.C_C_smul_of]
    exact Q.smul_mem _ ma

theorem pow_le_unitIdeal (H : TowerAx ρ res p mm) (one : ∀ e (i : ι), T e 0 {i})
    (hone : ∀ e i, p e 0 {i} (one (e + 1) i) = one e i) (i : ι)
    (Q : Submodule (MvPolynomial ι (MvPolynomial (Fin g) R)) (H.Tot hc {i}))
    (hQ : ∀ l, (H.ops hc {i}).of 0 0 ⟨ρ l • one (0 + 1) i,
      smul_mem_Ks H (Finset.singleton_nonempty i) (by simpa using rho_mem l) _⟩ ∈ Q) (e : ℕ) :
    Ideal.span (Set.range ρ) ^ (e + 1) ≤ unitIdeal hc H one i Q e := by
  have hS : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  induction e with
  | zero =>
    rw [zero_add, pow_one, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact ⟨_, hQ l⟩
  | succ e ih =>
    rw [pow_succ, Ideal.mul_le]
    intro u hu v hv
    obtain ⟨h, hm⟩ := ih hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      have hmem : u * ρ l ∈ Ideal.span (Set.range ρ) ^ (e + 1 + 1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul hu (rho_mem l)
      have h' := smul_mem_Ks H hS hmem (one (e + 1 + 1) i)
      refine ⟨h', ?_⟩
      have hb : p (e + 1) 0 {i} (u • one (e + 1 + 1) i) =
          ((⟨u • one (e + 1) i, h⟩ : Ks p e 0 {i}) : T (e + 1) 0 {i}) := by
        rw [map_smul, hone]
      have e1 : (⟨(u * ρ l) • one (e + 1 + 1) i, h'⟩ : Ks p (e + 1) 0 {i}) =
          (H.ops hc {i}).y l e 0 ⟨u • one (e + 1) i, h⟩ := by
        apply Subtype.ext
        change (u * ρ l) • one (e + 1 + 1) i = (H.yK l e 0 {i} ⟨u • one (e + 1) i, h⟩ : _)
        rw [H.coe_yK l hS _ _ hb, smul_smul, mul_comm]
      rw [e1, ← BiOps.C_X_smul_of]
      exact Q.smul_mem _ hm
    | zero => simpa using zero_mem (unitIdeal hc H one i Q (e + 1))
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact add_mem ha hb
    | smul c a _ ha =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ c ha

theorem pow_smul_add_mem {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (Q : Submodule A M)
    (x : A) {a b : M} (ha : ∃ k : ℕ, x ^ k • a ∈ Q) (hb : ∃ k : ℕ, x ^ k • b ∈ Q) :
    ∃ k : ℕ, x ^ k • (a + b) ∈ Q := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨k', hk'⟩ := hb
  refine ⟨k + k', ?_⟩
  rw [smul_add]
  refine add_mem ?_ ?_
  · rw [add_comm, pow_add, mul_smul]
    exact Q.smul_mem _ hk
  · rw [pow_add, mul_smul]
    exact Q.smul_mem _ hk'

theorem exists_pow_smul_mem (H : TowerAx ρ res p mm) (one : ∀ e (i : ι), T e 0 {i}) (i : ι)
    (hform : ∀ e t (a : T e t {i}), ∃ (k : ℕ) (q : MvPolynomial ι R) (t' : ℤ) (w : T e t' {i}),
      w ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e t' {i})) ∧
      (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc e {i}) t a =
        q • GrSum.of (hc e {i}) 0 (one e i) + GrSum.of (hc e {i}) t' w)
    (Q : Submodule (MvPolynomial ι (MvPolynomial (Fin g) R)) (H.Tot hc {i}))
    (hQ : ∀ e r (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)),
      (H.ops hc {i}).of e 0 ⟨r • one (e + 1) i,
        smul_mem_Ks H (Finset.singleton_nonempty i) hr _⟩ ∈ Q)
    (m : H.Tot hc {i}) :
    ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • m ∈ Q := by
  have hS : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  have hker : ∀ (e : ℕ) (t : ℤ) (x : T (e + 1) t {i}), x ∈ Ks p e t {i} ↔
      x ∈ Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t {i})) := by
    intro e t x
    rw [← H.ker_eq e t {i} hS, mem_Ks hS, LinearMap.mem_ker]
  induction m using (H.ops hc {i}).induction with
  | h0 => exact ⟨0, by simp⟩
  | hadd a b ha hb => exact pow_smul_add_mem Q _ ha hb
  | hof e t a =>
    obtain ⟨x, hx⟩ := a
    have hx' := (hker e t x).1 hx
    suffices hs : ∀ x ∈ Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t {i})),
        ∀ h : x ∈ Ks p e t {i}, ∃ k : ℕ,
          (MvPolynomial.X i : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k •
            (H.ops hc {i}).of e t ⟨x, h⟩ ∈ Q from hs x hx' hx
    intro x hx
    induction hx using Submodule.smul_induction_on' with
    | smul r hr y _ =>
      intro h
      obtain ⟨k, q, t', w, hw, e1⟩ := hform (e + 1) t y
      obtain ⟨Φ, hΦ1, hΦ2⟩ := exists_mulMap hc H hr hS
      have e2 := congrArg Φ e1
      rw [hΦ2, map_add, hΦ2, hΦ1, hΦ1, hΦ1, map_pow, MvPolynomial.map_X] at e2
      have hz : r • w = 0 := H.smul_eq_zero_of_mem (e := e + 1) hS (m := e + 1) (n := 1) rfl hr
        (by simpa using hw)
      have e3 : (⟨r • w, smul_mem_Ks H hS hr w⟩ : Ks p e t' {i}) = 0 := Subtype.ext hz
      rw [e3, map_zero, add_zero] at e2
      refine ⟨k, ?_⟩
      rw [show (⟨r • y, h⟩ : Ks p e t {i}) = ⟨r • y, smul_mem_Ks H hS hr y⟩ from rfl, e2]
      exact Q.smul_mem _ (hQ e r hr)
    | add a ha b hb iha ihb =>
      intro h
      have e1 : (⟨a + b, h⟩ : Ks p e t {i}) =
          ⟨a, (hker e t a).2 ha⟩ + ⟨b, (hker e t b).2 hb⟩ := rfl
      rw [e1, map_add]
      exact pow_smul_add_mem Q _ (iha _) (ihb _)

end Tower

theorem tot_singleton_finite_up_to_X :
    ∀ (ι : Type) [LinearOrder ι] (R : Type) [CommRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S) (H : TowerAx ρ res p mm) (one : ∀ e (i : ι), T e 0 {i}), (∀ e i, p e 0 {i} (one (e + 1) i) = one e i) → (∀ e i t (a : T e t {i}), ∃ (k : ℕ) (q : MvPolynomial ι R) (t' : ℤ) (w : T e t' {i}), w ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e t' {i})) ∧ (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc e {i}) t a = q • GrSum.of (hc e {i}) 0 (one e i) + GrSum.of (hc e {i}) t' w) → ∀ i : ι, ∃ s : Finset (H.Tot hc {i}), ∀ m : H.Tot hc {i}, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • m ∈ Submodule.span (MvPolynomial ι (MvPolynomial (Fin g) R)) (s : Set (H.Tot hc {i})) := by
  intro ι _ R _ g ρ T _ _ res p mm hc H one hone hform i
  classical
  have hS : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  let f : Fin g → H.Tot hc {i} := fun l => (H.ops hc {i}).of 0 0 ⟨ρ l • one (0 + 1) i,
    smul_mem_Ks H hS (by simpa using rho_mem l) _⟩
  refine ⟨Finset.univ.image f, fun m => ?_⟩
  set Q := Submodule.span (MvPolynomial ι (MvPolynomial (Fin g) R))
    ((Finset.univ.image f : Finset (H.Tot hc {i})) : Set (H.Tot hc {i})) with hQdef
  have hf : ∀ l, f l ∈ Q := fun l => Submodule.subset_span (by simp)
  refine exists_pow_smul_mem hc H one i (hform · i) Q (fun e r hr => ?_) m
  obtain ⟨_, h⟩ := pow_le_unitIdeal hc H one hone i Q hf e hr
  exact h

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingOperatorsUniformKernel
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace TowerAx

theorem exists_X_pow_smul_of {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ}
    {ρ : Fin g → R} {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)]
    [∀ e t S, Module R (T e t S)] {res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S'}
    {p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S} {mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S}
    (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S)
    (H : TowerAx ρ res p mm) (S : Finset ι) (j : ι) (k : ℕ) :
    ∀ (e : ℕ) (t : ℤ) (a : Ks p e t S), ∃ (t' : ℤ) (b : Ks p e t' S),
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • (H.ops hc S).of e t a =
        (H.ops hc S).of e t' b ∧
      (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc (e + 1) S) t (a : T (e + 1) t S) =
        GrSum.of (hc (e + 1) S) t' (b : T (e + 1) t' S) := by
  induction k with
  | zero => exact fun e t a => ⟨t, a, by simp, by simp⟩
  | succ k ih =>
    intro e t a
    obtain ⟨t', b, h1, h2⟩ := ih e t a
    refine ⟨t' + 1, H.xK j e t' S b, ?_, ?_⟩
    · rw [pow_succ', mul_smul, h1]
      exact BiOps.X_smul_of (H.ops hc S) j e t' b
    · rw [pow_succ', mul_smul, h2]
      exact GrSum.X_smul_of (hc (e + 1) S) j t' _

end TowerAx

theorem exists_X_pow_smul_eq_zero_of_resTot_eq_zero : ∀ (ι : Type) [LinearOrder ι] (R : Type) [CommRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S) (H : TowerAx ρ res p mm), (∀ e S j t (a : T e t S), S.Nonempty → res e t S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e S) t a = 0) → ∀ (S : Finset ι) (j : ι) (a : H.Tot hc S), S.Nonempty → H.resTot hc S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • a = 0 := by
  intro ι _ R _ g ρ T _ _ res p mm hc H hyp S j a hS hres
  classical
  obtain ⟨s, hs⟩ := (H.ops hc S).exists_finset_sum a
  have hq : ∀ q : ℕ × ℤ, ∃ k : ℕ,
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k •
        (H.ops hc S).of q.1 q.2 ((H.ops hc S).comp q.1 q.2 a) = 0 := by
    intro q
    have h0 : H.resK q.1 q.2 (Finset.subset_insert j S) ((H.ops hc S).comp q.1 q.2 a) = 0 := by
      rw [← TowerAx.comp_resTot, hres, map_zero]
    have h1 : res (q.1 + 1) q.2 S (insert j S) (Finset.subset_insert j S)
        ((H.ops hc S).comp q.1 q.2 a : T (q.1 + 1) q.2 S) = 0 := congrArg Subtype.val h0
    obtain ⟨k, hk⟩ := hyp (q.1 + 1) S j q.2 _ hS h1
    obtain ⟨t', b, e1, e2⟩ :=
      TowerAx.exists_X_pow_smul_of hc H S j k q.1 q.2 ((H.ops hc S).comp q.1 q.2 a)
    refine ⟨k, ?_⟩
    rw [e2] at hk
    have hb : b = 0 :=
      Subtype.ext (GrSum.of_injective (hc (q.1 + 1) S) t' (by rw [hk]; exact (map_zero _).symm))
    rw [e1, hb, map_zero]
  choose k hk using hq
  refine ⟨∑ q ∈ s, k q, ?_⟩
  rw [hs, Finset.smul_sum]
  refine Finset.sum_eq_zero fun q hqs => ?_
  obtain ⟨c, hc'⟩ := Nat.exists_eq_add_of_le' (Finset.single_le_sum (f := k)
    (fun _ _ => Nat.zero_le _) hqs)
  rw [hc', pow_add, mul_smul, hk, smul_zero]

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeSeriesSpecialValueRational
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem DL_int_valued {r : ℕ} (g : (Fin r → ℕ) → ℂ) (hg : ∀ m, ∃ z : ℤ, g m = (z : ℂ))
    (cs : List (Fin r)) : ∀ m, ∃ z : ℤ, DL cs g m = (z : ℂ) := by
  induction cs with
  | nil => exact hg
  | cons c cs ih =>
    intro m
    obtain ⟨z1, h1⟩ := ih (m + Pi.single c 1)
    obtain ⟨z2, h2⟩ := ih m
    refine ⟨z1 - z2, ?_⟩
    show DL cs g (m + Pi.single c 1) - DL cs g m = ((z1 - z2 : ℤ) : ℂ)
    rw [h1, h2]
    push_cast
    ring

theorem coneTerm_neg_nat {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ)
    (m : Fin r → ℕ) :
    coneTerm a b (-(p : ℂ)) m = ((∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p : ℝ) : ℂ) := by
  unfold coneTerm
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [neg_neg, Complex.cpow_natCast, Complex.ofReal_pow]

theorem tsum_mem_of_denominator {α : Type} (f : α → ℂ) (K l : ℕ) (hl : 0 < l)
    (hf : ∀ m, ∃ x : ℤ, ((l : ℂ) ^ K) * f m = (x : ℂ)) :
    ∃ (q : ℚ) (z : ℤ), ∑' m, f m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  have hmem : ((l : ℂ) ^ K) * ∑' m, f m ∈ Set.range (Int.cast : ℤ → ℂ) := by
    by_cases hs : Summable f
    · rw [← tsum_mul_left]
      have hs' : Summable (fun m => (l : ℂ) ^ K * f m) := hs.mul_left _
      apply Complex.isClosed_range_intCast.mem_of_tendsto hs'.hasSum
      refine Filter.Eventually.of_forall (fun S => ?_)
      choose x hx using hf
      exact ⟨∑ b ∈ S, x b, by push_cast; exact Finset.sum_congr rfl (fun b _ => (hx b).symm)⟩
    · rw [tsum_eq_zero_of_not_summable hs, mul_zero]
      exact ⟨0, by simp⟩
  obtain ⟨z, hz⟩ := hmem
  have hlC : ((l : ℂ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')
  have hlQ : ((l : ℚ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')
  refine ⟨(z : ℚ) / (l : ℚ) ^ K, z, ?_, ?_⟩
  · push_cast
    rw [hz]
    exact (mul_div_cancel_left₀ (∑' m, f m) hlC).symm
  · rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ hlQ

theorem value_neg_nat_mem : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (p K l : ℕ), 0 < l → (∀ m, ∃ z : ℤ, (l : ℚ) ^ K * u m = z) → (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (z : ℤ), ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  intro ι _ r a b u cs p K l hl hu hprod
  apply tsum_mem_of_denominator _ K l hl
  intro m
  obtain ⟨z2, h2⟩ := DL_int_valued (coneTerm a b (-(p : ℂ))) (fun m' => by
      obtain ⟨z, hz⟩ := hprod m'
      exact ⟨z, by rw [coneTerm_neg_nat, hz, Complex.ofReal_intCast]⟩) cs m
  obtain ⟨z1, h1⟩ := hu m
  refine ⟨z1 * z2, ?_⟩
  rw [h2, ← mul_assoc]
  have h1' : ((l : ℂ) ^ K) * (u m : ℂ) = (z1 : ℂ) := by exact_mod_cast h1
  rw [h1']
  push_cast
  ring

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsQuot
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerAct

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d}

def val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) : T.1.A :=
  PAlg.Hom.f φ.1 (𝒯.c k 0).val

theorem val_comp (𝒯 : Tower κ s) {T T' : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (ψ : T ⟶ T') (k : Fin d) :
    val 𝒯 (φ ≫ ψ) k = PAlg.Hom.f ψ.1 (val 𝒯 φ k) := rfl

theorem sharp_val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    T.1.sharp (val 𝒯 φ k) = mapU φ.1 (𝒯.g (s.T k)) := by
  rw [val, ← mapU_sharp]
  exact congrArg (mapU φ.1) (𝒯.c_sharp k)

def valU (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) : (T.1.A)ˣ :=
  Units.map (PAlg.Hom.f φ.1).toMonoidHom (𝒯.c k 0)

theorem valU_val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    ((valU 𝒯 φ k : (T.1.A)ˣ) : T.1.A) = val 𝒯 φ k := rfl

theorem hom_ext (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ ψ : 𝒯.obj ⟶ T)
    (h : ∀ k, val 𝒯 φ k = val 𝒯 ψ k) : φ = ψ := by
  obtain ⟨g, -, hg, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hu : ∀ k, T.1.sharp (val 𝒯 φ k) = g (s.T k) := fun k => by
    rw [sharp_val]
    exact RingHom.congr_fun (hg φ) _
  obtain ⟨χ, -, hχ⟩ := huniq (fun k => val 𝒯 φ k) hu
  exact (hχ φ (fun k => rfl)).trans (hχ ψ (fun k => (h k).symm)).symm

theorem sharp_mem (ε : Eps l) {T : (F.pt κ).Elements} (x : (epsU ε (F.pt κ)).U T) :
    T.1.sharp ((x.1 : (T.1.A)ˣ) : T.1.A) = 1 := by
  have hx : Units.map T.1.sharp x.1 = 1 := x.2
  exact congrArg Units.val hx

theorem exists_act (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) :
    ∃ ψ : 𝒯.obj ⟶ T, ∀ k, val 𝒯 ψ k = ((a k).1 : T.1.A) * val 𝒯 φ k := by
  obtain ⟨g, -, hg, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hu : ∀ k, T.1.sharp (((a k).1 : T.1.A) * val 𝒯 φ k) = g (s.T k) := fun k => by
    rw [map_mul, sharp_mem ε (a k), one_mul, sharp_val]
    exact RingHom.congr_fun (hg φ) _
  obtain ⟨χ, hχ, -⟩ := huniq _ hu
  exact ⟨χ, fun k => hχ k⟩

def act (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) : 𝒯.obj ⟶ T :=
  (exists_act 𝒯 ε a φ).choose

theorem act_val (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    val 𝒯 (act 𝒯 ε a φ) k = ((a k).1 : T.1.A) * val 𝒯 φ k :=
  (exists_act 𝒯 ε a φ).choose_spec k

theorem exists_quot (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements} (φ ψ : 𝒯.obj ⟶ T) :
    ∃ a : Fin d → (epsU ε (F.pt κ)).U T, ∀ k, ((a k).1 : T.1.A) * val 𝒯 φ k = val 𝒯 ψ k := by
  obtain ⟨g, -, hg, -⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hs : ∀ (χ : 𝒯.obj ⟶ T) k, T.1.sharp (val 𝒯 χ k) = g (s.T k) := fun χ k => by
    rw [sharp_val]
    exact RingHom.congr_fun (hg χ) _
  refine ⟨fun k => ⟨valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹, ?_⟩, fun k => ?_⟩
  · show Units.map T.1.sharp (valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, valU_val, valU_val, hs ψ k, hs φ k]
  · show ((valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹ : (T.1.A)ˣ) : T.1.A) * val 𝒯 φ k = val 𝒯 ψ k
    rw [← valU_val 𝒯 φ k, ← Units.val_mul, inv_mul_cancel_right, valU_val]

theorem act_unique (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a b : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (h : act 𝒯 ε a φ = act 𝒯 ε b φ) : a = b := by
  funext k
  have h1 := act_val 𝒯 ε a φ k
  rw [h, act_val, ← valU_val 𝒯 φ k] at h1
  apply Subtype.ext
  apply Units.ext
  exact ((valU 𝒯 φ k).isUnit.mul_left_inj).1 h1.symm

theorem tower_act : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (ε : Eps l), ∃ A : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj, ∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d), PAlg.Hom.f (A.act a φ).1 (𝒯.c k 0).val = ((a k).1 : T.1.A) * PAlg.Hom.f φ.1 (𝒯.c k 0).val := by
  intro l _ O _ F κ d s 𝒯 ε
  refine ⟨{ act := fun a φ => act 𝒯 ε a φ
            act_one := fun c => hom_ext 𝒯 _ _ fun k => by
              rw [act_val]
              exact one_mul _
            act_mul := fun a b c => hom_ext 𝒯 _ _ fun k => by
              rw [act_val, act_val, act_val, ← mul_assoc]
              rfl
            act_comp := fun a c φ => hom_ext 𝒯 _ _ fun k => by
              rw [val_comp, act_val, act_val, val_comp, map_mul]
              rfl
            ne := fun t => by
              obtain ⟨g, -, -, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 ((jE (F.pt κ)).obj t)
              choose u hu using fun k => PAlg.IsTest.sharp_surjective t.1.property (g (s.T k))
              obtain ⟨χ, -, -⟩ := huniq u hu
              exact ⟨χ⟩
            trans := fun t c c' => by
              obtain ⟨a, ha⟩ := exists_quot 𝒯 ε c c'
              have hac : act 𝒯 ε a c = c' := hom_ext 𝒯 _ _ fun k => by rw [act_val, ha]
              exact ⟨a, hac, fun b hb => act_unique 𝒯 ε b a c (hb.trans hac.symm)⟩ }, ?_⟩
  intro T a φ k
  exact act_val 𝒯 ε a φ k

end GlobalTheory.CompanionTheory.TowerAct
end
end

