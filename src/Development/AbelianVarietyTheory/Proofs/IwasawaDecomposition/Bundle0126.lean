import Mathlib
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0122
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0121
import Formalism.GaloisCohomology.Statement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfEqOnCoprime
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.QuadPrim

def IsPrimQuad (L : ℕ) (f : ℕ → ℂ) : Prop :=
  (∃ ψ : DirichletCharacter ℂ L, ψ.IsPrimitive ∧ ∀ a : ℕ, ψ (a : ZMod L) = f a) ∧
    ∀ a : ℕ, f a = 0 ∨ f a = 1 ∨ f a = -1

theorem changeLevel_nat {n m : ℕ} (χ : DirichletCharacter ℂ n) (hm : n ∣ m) {a : ℕ}
    (ha : a.Coprime m) :
    DirichletCharacter.changeLevel hm χ (a : ZMod m) = χ (a : ZMod n) := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hm (a := (a : ℤ))
    (Nat.isCoprime_iff_coprime.mpr ha)
  simpa using this

theorem apply_nat_eq_zero {n : ℕ} (χ : DirichletCharacter ℂ n) {a : ℕ} (ha : ¬ a.Coprime n) :
    χ (a : ZMod n) = 0 :=
  χ.map_nonunit (fun h => ha ((ZMod.isUnit_iff_coprime a n).mp h))

theorem isPrimitive_mul {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) :
    DirichletCharacter.IsPrimitive
      (DirichletCharacter.changeLevel (dvd_mul_right m n) α *
        DirichletCharacter.changeLevel (dvd_mul_left n m) β) := by
  have : NeZero (m * n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  set A := DirichletCharacter.changeLevel (dvd_mul_right m n) α with hA
  set B := DirichletCharacter.changeLevel (dvd_mul_left n m) β with hB
  have cA : A.conductor = m := by
    rw [hA, DirichletCharacter.conductor_changeLevel]; exact hα
  have cB : B.conductor = n := by
    rw [hB, DirichletCharacter.conductor_changeLevel]; exact hβ
  have h1 := DirichletCharacter.conductor_mul_dvd_lcm_conductor (A * B) B⁻¹
  have h2 := DirichletCharacter.conductor_mul_dvd_lcm_conductor (A * B) A⁻¹
  rw [mul_inv_cancel_right, DirichletCharacter.conductor_inv, cA, cB] at h1
  rw [mul_inv_cancel_comm, DirichletCharacter.conductor_inv, cA, cB] at h2
  have h3 : m ∣ DirichletCharacter.conductor (A * B) :=
    h.dvd_of_dvd_mul_right (h1.trans (Nat.lcm_dvd_mul _ _))
  have h4 : n ∣ DirichletCharacter.conductor (A * B) :=
    h.symm.dvd_of_dvd_mul_right (h2.trans (Nat.lcm_dvd_mul _ _))
  exact Nat.dvd_antisymm (DirichletCharacter.conductor_dvd_level _)
    (h.mul_dvd_of_dvd_of_dvd h3 h4)

theorem eq_of_eqOn_coprime {N L M : ℕ} [NeZero N] [NeZero L] (hM : M ≠ 0)
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ L)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (h : ∀ a : ℕ, a.Coprime M → χ (a : ZMod N) = ψ (a : ZMod L)) :
    N = L ∧ ∀ a : ℕ, χ (a : ZMod N) = ψ (a : ZMod L) := by
  have : NeZero (N * L * M) := ⟨mul_ne_zero (mul_ne_zero (NeZero.ne N) (NeZero.ne L)) hM⟩
  have hN : N ∣ N * L * M := (dvd_mul_right N L).mul_right M
  have hL : L ∣ N * L * M := (dvd_mul_left L N).mul_right M
  have key : DirichletCharacter.changeLevel hN χ = DirichletCharacter.changeLevel hL ψ := by
    apply MulChar.ext
    intro u
    have hu := ZMod.val_coe_unit_coprime u
    rw [← ZMod.natCast_zmod_val (u : ZMod (N * L * M)), changeLevel_nat χ hN hu,
      changeLevel_nat ψ hL hu]
    exact h _ (hu.coprime_dvd_right (dvd_mul_left M _))
  have hNL : N = L := by
    have := congrArg DirichletCharacter.conductor key
    rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at this
    exact hχ.symm.trans (this.trans hψ)
  subst hNL
  refine ⟨rfl, fun a => ?_⟩
  rw [DirichletCharacter.changeLevel_injective hN key]

theorem IsPrimQuad.mul {m n : ℕ} {f g : ℕ → ℂ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m.Coprime n)
    (hf : IsPrimQuad m f) (hg : IsPrimQuad n g) : IsPrimQuad (m * n) (fun a => f a * g a) := by
  have : NeZero m := ⟨hm⟩
  have : NeZero n := ⟨hn⟩
  obtain ⟨⟨α, hα, hαf⟩, hf⟩ := hf
  obtain ⟨⟨β, hβ, hβg⟩, hg⟩ := hg
  refine ⟨⟨_, isPrimitive_mul h α β hα hβ, fun a => ?_⟩, fun a => ?_⟩
  · by_cases ha : a.Coprime (m * n)
    · rw [MulChar.mul_apply, changeLevel_nat _ _ ha, changeLevel_nat _ _ ha, hαf, hβg]
    · rw [apply_nat_eq_zero _ ha]
      rw [Nat.coprime_mul_iff_right, not_and_or] at ha
      beta_reduce
      rcases ha with ha | ha
      · rw [← hαf, apply_nat_eq_zero _ ha, zero_mul]
      · rw [← hβg, apply_nat_eq_zero _ ha, mul_zero]
  · rcases hf a with h1 | h1 | h1 <;> rcases hg a with h2 | h2 | h2 <;> simp [h1, h2]

theorem IsPrimQuad.pow {m : ℕ} {f : ℕ → ℂ} (hf : IsPrimQuad m f) (k : Fin 2) :
    IsPrimQuad (m ^ k.1) (fun a => f a ^ k.1) := by
  fin_cases k
  · show IsPrimQuad 1 (fun a => f a ^ 0)
    refine ⟨⟨1, DirichletCharacter.isPrimitive_one_level_one, fun a => ?_⟩, fun a => by simp⟩
    rw [MulChar.one_apply (isUnit_of_subsingleton _)]
    simp
  · simpa using hf

theorem isPrimQuad_jacobi {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    IsPrimQuad p (fun a => ((jacobiSym (a : ℤ) p : ℤ) : ℂ)) := by
  have := Fact.mk hp
  refine ⟨⟨(quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ), ?_, fun a => ?_⟩,
    fun a => ?_⟩
  · rcases (Nat.dvd_prime hp).mp (DirichletCharacter.conductor_dvd_level
      ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) with h | h
    · exfalso
      rw [← DirichletCharacter.eq_one_iff_conductor_eq_one,
        MulChar.ringHomComp_eq_one_iff (RingHom.injective_int _)] at h
      exact quadraticChar_ne_one (by rwa [ZMod.ringChar_zmod_n]) h
    · exact h
  · beta_reduce
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
    simp
  · rcases jacobiSym.trichotomy (a : ℤ) p with h | h | h <;> simp [h]

theorem isPrimQuad_chi8 :
    IsPrimQuad 8 (fun a => ((ZMod.χ₈ (a : ZMod 8) : ℤ) : ℂ)) := by
  refine ⟨⟨ZMod.χ₈.ringHomComp (Int.castRingHom ℂ), ?_, fun a => by simp⟩, fun a => ?_⟩
  · set χ : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ) with hχ
    by_contra hne
    have hd := DirichletCharacter.conductor_dvd_level χ
    have h4 : χ.conductor ∣ 4 := by
      have hle := Nat.le_of_dvd (by norm_num) hd
      have hne' : χ.conductor ≠ 8 := hne
      generalize χ.conductor = c at hd hle hne'
      interval_cases c <;> simp_all
    obtain ⟨h48, χ₀, h0⟩ := (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ
      (show 4 ∣ 8 by norm_num)).mpr h4
    have e1 : χ ((5 : ℕ) : ZMod 8) = χ₀ ((5 : ℕ) : ZMod 4) := by
      rw [h0]; exact changeLevel_nat χ₀ h48 (by norm_num)
    have e2 : ((5 : ℕ) : ZMod 4) = 1 := by decide
    have e3 : ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 := by decide
    rw [e2, map_one, hχ, MulChar.ringHomComp_apply, e3] at e1
    norm_num at e1
  · rcases ZMod.isQuadratic_χ₈ (a : ZMod 8) with h | h | h <;> simp [h]

theorem main : ∀ q d : ℕ, q.Prime → d.Prime → q % 4 = 3 → d % 4 = 3 → q ≠ d → ∀ (i j k : Fin 2), (i.1 + j.1 ≠ 0) → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), GlobalTheoryTheory.Induces χ (fun a => GlobalTheoryTheory.chi8 a ^ k.1 * GlobalTheoryTheory.chDir d a ^ j.1 * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d) → N = 8 ^ k.1 * d ^ j.1 * q ^ i.1 ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧ GlobalTheoryTheory.IsRealChar χ ∧ ∀ a : ℕ, 0 < a → (k.1 = 0 → χ (a : ZMod N) = GlobalTheoryTheory.chDir d a ^ j.1 * GlobalTheoryTheory.psDir q a ^ i.1) := by
  intro q d hq hd hq4 hd4 hqd i j k hij N _ χ hχ
  obtain ⟨hK, hK2⟩ := GlobalTheory.kronSym_neg_eq_jacobiSym_and_two
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have c8 : ∀ p : ℕ, p.Prime → p ≠ 2 → Nat.Coprime 8 p := fun p hp h2 =>
    Nat.Coprime.pow_left 3 ((Nat.coprime_primes Nat.prime_two hp).mpr h2.symm)
  have cdq : Nat.Coprime d q := (Nat.coprime_primes hd hq).mpr hqd.symm
  have n8 : (8 : ℕ) ^ k.1 ≠ 0 := pow_ne_zero _ (by norm_num)
  have nd : d ^ j.1 ≠ 0 := pow_ne_zero _ hd.ne_zero
  have nq : q ^ i.1 ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hP := ((isPrimQuad_chi8.pow k).mul n8 nd (Nat.Coprime.pow _ _ (c8 d hd hd2))
    ((isPrimQuad_jacobi hd hd2).pow j)).mul (mul_ne_zero n8 nd) nq
    (Nat.Coprime.mul_left (Nat.Coprime.pow _ _ (c8 q hq hq2)) (Nat.Coprime.pow _ _ cdq))
    ((isPrimQuad_jacobi hq hq2).pow i)
  obtain ⟨⟨ψ, hψ, hψf⟩, htri⟩ := hP
  have : NeZero (8 ^ k.1 * d ^ j.1 * q ^ i.1) := ⟨mul_ne_zero (mul_ne_zero n8 nd) nq⟩
  have hch : ∀ a : ℕ, 0 < a → GlobalTheoryTheory.chDir d a = ((jacobiSym (a : ℤ) d : ℤ) : ℂ) := by
    intro a ha
    rw [GlobalTheoryTheory.chDir, GlobalTheoryTheory.kron, hK d a hd4 ha]
  have hps : ∀ a : ℕ, 0 < a → GlobalTheoryTheory.psDir q a = ((jacobiSym (a : ℤ) q : ℤ) : ℂ) := by
    intro a ha
    rw [GlobalTheoryTheory.psDir, GlobalTheoryTheory.kron, hK q a hq4 ha]
  obtain ⟨hN, hval⟩ := eq_of_eqOn_coprime (M := 8 * q * d)
    (mul_ne_zero (mul_ne_zero (by norm_num) hq.ne_zero) hd.ne_zero) χ ψ hχ.1 hψ (by
      intro a ha
      have hodd : Odd a := by
        have : a.Coprime 2 := ha.coprime_dvd_right
          (((show 2 ∣ 8 by norm_num).mul_right q).mul_right d)
        exact Nat.coprime_two_right.mp this
      rw [hχ.2 a ha, hψf]
      beta_reduce
      rw [hch a hodd.pos, hps a hodd.pos, GlobalTheoryTheory.chi8, GlobalTheoryTheory.kron, hK2 a hodd])
  have hquad : χ.IsQuadratic := by
    intro x
    rw [← ZMod.natCast_zmod_val x, hval, hψf]
    exact htri _
  refine ⟨hN, hquad.sq_eq_one, ?_, ?_, ?_⟩
  · intro h1
    have hc : N = 1 := hχ.1.symm.trans (DirichletCharacter.eq_one_iff_conductor_eq_one.mp h1)
    rw [hc] at hN
    have h2 := Nat.eq_one_of_mul_eq_one_left hN.symm
    have h3 := Nat.eq_one_of_mul_eq_one_left (Nat.eq_one_of_mul_eq_one_right hN.symm)
    rw [Nat.pow_eq_one] at h2 h3
    omega
  · intro x
    rcases hquad x with h | h | h <;> simp [h]
  · intro a ha hk
    rw [hval, hψf, hch a ha, hps a ha]
    simp [hk]

end GlobalTheory.QuadPrim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Matrix

namespace GlobalTheory.CuspRep.LocUniq

theorem equiv_of_iSup_range {R M S S' : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [AddCommGroup S'] [Module R S'] [IsSimpleModule R S] [IsSimpleModule R S']
    (h : ∀ x : M, x ∈ ⨆ f : S →ₗ[R] M, LinearMap.range f) (g : S' →ₗ[R] M) (hg : Function.Injective g) :
    Nonempty (S ≃ₗ[R] S') := by
  let s : Set (Submodule R M) := {m | Nonempty (m ≃ₗ[R] S)}
  have : ∀ m : s, IsSimpleModule R m := fun m => m.2.elim fun e => IsSimpleModule.congr e
  have e0 := LinearEquiv.ofInjective g hg
  have : IsSimpleModule R (LinearMap.range g) := IsSimpleModule.congr e0.symm
  have hle : LinearMap.range g ≤ sSup s := fun x _ => by
    refine (iSup_le (a := sSup s) fun f => ?_) (h x)
    rcases LinearMap.injective_or_eq_zero f with hf | rfl
    · exact le_sSup ⟨(LinearEquiv.ofInjective f hf).symm⟩
    · simp
  obtain ⟨m, ⟨e⟩, ⟨e'⟩⟩ := (LinearMap.range g).linearEquiv_of_le_sSup s hle
  exact ⟨(e0.trans (e'.trans e)).symm⟩

section Rep

variable {G V W W' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def isoPart (σ : Representation ℂ G W) (ρ : Representation ℂ G V) : Submodule ℂ V :=
  ⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap

theorem isoPart_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V} (hx : x ∈ isoPart σ ρ) :
    ρ g x ∈ isoPart σ ρ := by
  refine (iSup_le (a := (isoPart σ ρ).comap (ρ g)) fun f => ?_) hx
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, LinearMap.congr_fun (f.isIntertwining' g) v⟩

theorem isoPart_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V} (hx : x ∈ isoPart σ ρ) : T x ∈ isoPart σ ρ := by
  refine (iSup_le (a := (isoPart σ ρ).comap T) fun f => ?_) hx
  rintro _ ⟨v, rfl⟩
  refine Submodule.mem_iSup_of_mem (⟨T ∘ₗ f.toLinearMap, fun g => LinearMap.ext fun u => ?_⟩ : σ.IntertwiningMap ρ)
    ⟨v, rfl⟩
  exact (congrArg T (LinearMap.congr_fun (f.isIntertwining' g) u)).trans (hT g _)

theorem equiv_of_isoPart (σ : Representation ℂ G W) (σ' : Representation ℂ G W') (ρ : Representation ℂ G V)
    [σ.IsIrreducible] [σ'.IsIrreducible] (h : isoPart σ ρ = ⊤) (f' : σ'.IntertwiningMap ρ) (hf' : f' ≠ 0) :
    Nonempty (σ.Equiv σ') := by
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f').resolve_right hf'
  obtain ⟨e⟩ := equiv_of_iSup_range (R := MonoidAlgebra ℂ G) (S := σ.asModule) (M := ρ.asModule) (fun x => by
    have hx : ρ.asModuleEquiv x ∈ isoPart σ ρ := h ▸ Submodule.mem_top
    have hle : isoPart σ ρ ≤ ((⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule,
        LinearMap.range f).restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      have : Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f (σ.asModuleEquiv.symm v) ∈
          ⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule, LinearMap.range f :=
        Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f) ⟨_, rfl⟩
      exact this
    exact hle hx) (Representation.IntertwiningMap.equivLinearMapAsModule σ' ρ f') hi
  exact ⟨((Representation.IntertwiningMap.equivLinearMapAsModule σ σ').symm e.toLinearMap).ofBijective e.bijective⟩

end Rep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem gl_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ v, GeneralLinearGroup.map (pLoc E v) g = GeneralLinearGroup.map (pLoc E v) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext E fun v => ?_)
  exact congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x.val i j) (H v)

theorem comm_locGL (w : HeightOneSpectrum (𝓞 E)) {k : GL (Fin a) (Af E)}
    (hk : GeneralLinearGroup.map (pLoc E w) k = 1) (g : GL (Fin a) (w.adicCompletion E)) :
    k * locGL E a w g = locGL E a w g * k := by
  refine gl_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases h : v = w
  · subst h; rw [hk, one_mul, mul_one]
  · rw [pLoc_locGL_of_ne h, one_mul, mul_one]

theorem isoPart_fin {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin a) (Af E)) V)
    (w : HeightOneSpectrum (𝓞 E)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W) (k : GL (Fin a) (Af E)) {x : V}
    (hx : x ∈ isoPart σ (τ.comp (locGL E a w))) : τ k x ∈ isoPart σ (τ.comp (locGL E a w)) := by
  obtain ⟨g, hg⟩ : ∃ g, g = GeneralLinearGroup.map (pLoc E w) k := ⟨_, rfl⟩
  have hk : GeneralLinearGroup.map (pLoc E w) ((locGL E a w g)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, pLoc_locGL, hg, inv_mul_cancel]
  have h1 := isoPart_act σ _ g (isoPart_comm σ _ (τ ((locGL E a w g)⁻¹ * k)) (fun g' y => by
    simp only [MonoidHom.comp_apply]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, comm_locGL w hk]) hx)
  rwa [MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1

variable [IsTotallyComplex E]

theorem isoPart_op (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W) (o : Op E a) {x : π.V}
    (hx : x ∈ isoPart σ (π.locRep w)) : π.op o x ∈ isoPart σ (π.locRep w) := by
  cases o with
  | fin k =>
    exact isoPart_fin π.finPart w σ k hx
  | cpt k =>
    refine isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
      (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1

theorem isLocComp_unique (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))) (h : π.IsLocComp w σ) (h' : π.IsLocComp w σ') :
    Nonempty (σ.ρ.Equiv σ'.ρ) := by
  obtain ⟨f, h0, hf⟩ := h
  obtain ⟨f', h0', hf'⟩ := h'
  have := σ.irred
  have := σ'.irred
  refine equiv_of_isoPart σ.ρ σ'.ρ (π.locRep w) ?_ ⟨f', fun g => LinearMap.ext (hf' g)⟩
    fun e => h0' (congrArg Representation.IntertwiningMap.toLinearMap e)
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  rcases π.irred ((isoPart σ.ρ (π.locRep w)).map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, isoPart_op π w σ.ρ o hx, rfl⟩) with h1 | h1
  · refine absurd (LinearMap.ext fun v => ?_) h0
    have h2 : isoPart σ.ρ (π.locRep w) = ⊥ := hi (h1.trans (Submodule.map_bot _).symm)
    have h3 : f v ∈ isoPart σ.ρ (π.locRep w) :=
      Submodule.mem_iSup_of_mem (⟨f, fun g => LinearMap.ext (hf g)⟩ : σ.ρ.IntertwiningMap (π.locRep w)) ⟨v, rfl⟩
    rw [h2] at h3
    exact h3
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)

end GlobalTheory.CuspRep.LocUniq

theorem GlobalTheory.CuspRep.CG.IsLoc.unique : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a) (w : HeightOneSpectrum (𝓞 E)) (σ σ' : Irr (GL (Fin a) (w.adicCompletion E))), π.IsLoc w σ → π.IsLoc w σ' → σ = σ' := by
  intro E _ _ _ a π w σ σ' h h'
  induction π using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  induction σ' using Quotient.inductionOn
  exact Quotient.sound (GlobalTheory.CuspRep.LocUniq.isLocComp_unique _ w _ _ h h')
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolSplit

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {r : ℕ}

theorem map_sigR {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A σ z) =
      sigR B σ ((Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_JR {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B)
    (J : Matrix (Fin r) (Fin r) E) :
    (JR A J).map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = JR B J := by
  ext i j; simp [JR, inclR]

theorem map_unit {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B)
    (J : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (A ⊗[F] E)) :
    (Formalism.UG.cT (sigR A σ) g * JR A J * g).map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom =
      Formalism.UG.cT (sigR B σ) (g.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom) * JR B J *
        g.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom := by
  rw [Matrix.map_mul, Matrix.map_mul, map_JR]
  congr 2
  ext i j
  exact map_sigR σ p _

end Gen

theorem exists_adelic_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), ∃ e : HA (AF F) σ J ≃ₜ* HA (Ainf F) σ J × HA (Af F) σ J, ∀ h, ((HA.mat (Af F) σ J (e h).2 : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) = finMat σ J h ∧ ((HA.mat (Ainf F) σ J (e h).1 : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)) = ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) := by
  intro F E _ _ _ _ _ σ r J
  let pInf : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  let pFin : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  obtain ⟨e, he, hc, hc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have ext : ∀ {M N : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}, M.map pInf = N.map pInf → M.map pFin = N.map pFin →
      M = N := fun {M N} h1 h2 => by
    ext i j
    refine e.injective (Prod.ext ?_ ?_)
    · rw [(he _).1, (he _).1]; exact congrFun (congrFun h1 i) j
    · rw [(he _).2, (he _).2]; exact congrFun (congrFun h2 i) j
  let gl : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E) → Matrix (Fin r) (Fin r) (Af F ⊗[F] E) →
      Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := fun M N => Matrix.of fun i j => e.symm (M i j, N i j)
  have g1 : ∀ M N, (gl M N).map pInf = M := fun M N => by
    ext i j
    exact ((he _).1.symm.trans (congrArg Prod.fst (e.apply_symm_apply _)))
  have g2 : ∀ M N, (gl M N).map pFin = N := fun M N => by
    ext i j
    exact ((he _).2.symm.trans (congrArg Prod.snd (e.apply_symm_apply _)))
  let χ : HA (AF F) σ J →* HA (Ainf F) σ J × HA (Af F) σ J :=
    { toFun := fun h => ((⟨Formalism.UG.bc pInf (HA.mat _ _ _ h), (by
          have := congrArg (fun M => M.map pInf) (show Formalism.UG.cT _ _ * _ * _ = _ from h.2)
          rw [map_unit σ (fstA F), map_JR (fstA F)] at this
          exact this)⟩ : HR (Ainf F) σ J),
        (⟨Formalism.UG.bc pFin (HA.mat _ _ _ h), (by
          have := congrArg (fun M => M.map pFin) (show Formalism.UG.cT _ _ * _ * _ = _ from h.2)
          rw [map_unit σ (sndA F), map_JR (sndA F)] at this
          exact this)⟩ : HR (Af F) σ J))
      map_one' := Prod.ext (Subtype.ext (map_one (Formalism.UG.bc pInf))) (Subtype.ext (map_one (Formalism.UG.bc pFin)))
      map_mul' := fun a b => Prod.ext (Subtype.ext (map_mul (Formalism.UG.bc pInf) _ _))
        (Subtype.ext (map_mul (Formalism.UG.bc pFin) _ _)) }
  let ω : HA (Ainf F) σ J × HA (Af F) σ J → HA (AF F) σ J := fun g =>
    (⟨⟨gl g.1.1.val g.2.1.val, gl g.1.1.inv g.2.1.inv,
      ext (by rw [Matrix.map_mul, g1, g1, g.1.1.val_inv]; simp) (by rw [Matrix.map_mul, g2, g2, g.2.1.val_inv]; simp),
      ext (by rw [Matrix.map_mul, g1, g1, g.1.1.inv_val]; simp) (by rw [Matrix.map_mul, g2, g2, g.2.1.inv_val]; simp)⟩,
      ext ((map_unit σ (fstA F) J _).trans (Eq.trans (by
        rw [g1]
        exact g.1.2) (map_JR (fstA F) J).symm)) ((map_unit σ (sndA F) J _).trans (Eq.trans (by
        rw [g2]
        exact g.2.2) (map_JR (sndA F) J).symm))⟩ : HR (AF F) σ J)
  have l1 : Function.LeftInverse ω χ := fun h => Subtype.ext (Units.ext (ext (g1 _ _) (g2 _ _)))
  have l2 : Function.RightInverse ω χ := fun g =>
    Prod.ext (Subtype.ext (Units.ext (g1 _ _))) (Subtype.ext (Units.ext (g2 _ _)))
  let ψ : HA (AF F) σ J ≃* HA (Ainf F) σ J × HA (Af F) σ J :=
    { χ with invFun := ω, left_inv := l1, right_inv := l2 }
  have hp1 : Continuous pInf := (continuous_fst.comp hc).congr fun z => (he z).1
  have hp2 : Continuous pFin := (continuous_snd.comp hc).congr fun z => (he z).2
  have hv : Continuous fun h : HA (AF F) σ J => HA.mat _ _ _ h := continuous_subtype_val
  have c1 : Continuous ψ := by
    refine Continuous.prodMk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _)
      (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _)
    · exact (Units.continuous_val.comp hv).matrix_map hp1
    · exact (Units.continuous_coe_inv.comp hv).matrix_map hp1
    · exact (Units.continuous_val.comp hv).matrix_map hp2
    · exact (Units.continuous_coe_inv.comp hv).matrix_map hp2
  have c2 : Continuous ψ.symm := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk ?_ ?_)
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)).matrix_elem i j
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk ?_ ?_)
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)).matrix_elem i j
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j
  exact ⟨{ ψ with continuous_toFun := c1, continuous_invFun := c2 }, fun h => ⟨rfl, rfl⟩⟩

end GlobalTheory.Mem.VolSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem exists_isFdeg_smul_of_isDS : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → ∀ c : NNReal, 0 < c → ∃ d : ℝ, IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d := by
  intro n ε lam H _ _ σ h c hc
  obtain ⟨h1, h2, hU, hirr, hsq, -⟩ := h
  obtain ⟨d, hd, hI⟩ := GlobalTheory.schur_orthogonality_unitary n ε H σ hU hirr hsq
  have hc' : (0 : ℝ) < (c : ℝ) := hc
  refine ⟨d / c, div_pos hd hc', fun v w v' w' => ⟨(hI v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
  rw [integral_smul_measure, (hI v w v' w').2, ENNReal.coe_toReal, Complex.real_smul,
    Complex.ofReal_div, div_div_eq_mul_div]
  ring

end GlobalTheory.Mem.Vol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalGaloisDataShaLengthEqStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localGaloisData_shaLength_eq : ∀ {F Ω Ω' : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field Ω'] [Algebra F Ω'] [IsAlgClosure F Ω'] (l : ℕ) [Fact l.Prime] (D : Formalism.GaloisCohomology.LData F Ω l), ∃ D' : Formalism.GaloisCohomology.LData F Ω' l, ∀ e : ℤ, Formalism.GaloisCohomology.shaLen D' e = Formalism.GaloisCohomology.shaLen D e := by
  first | exact @GlobalTheory.ShaTransport.exists_lData_shaLen_eq | exact GlobalTheory.ShaTransport.exists_lData_shaLen_eq | (intros; apply GlobalTheory.ShaTransport.exists_lData_shaLen_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistEmptyLocalStatement
section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twist_empty_local : ∀ (B : Base) (C : Cols B) (W : RowsRest B C) (nd : NData B.R B.host W.what₂), IsEmpty nd.Loc → ∃ tw : NTw B.R B.host W.what₂ B.LL0 nd, IsEmpty tw.Tw := by
  first | exact @GlobalTheory.MemN.exists_nTw_empty | exact GlobalTheory.MemN.exists_nTw_empty | (intros; apply GlobalTheory.MemN.exists_nTw_empty <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMuZeroCharactersOfSplitTypePrimesAlStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mu0Exists_of_splits_of_integral_of_MUQ : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ), (∀ k, SplitsC H.E (H.g k)) → (∀ τ, ∃ z : ℤ, e τ = z) → UpperTheory.MUQ (embPsi H) e → Mu0Exists P W e j := by
  first | exact @GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes | exact GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes | (intros; apply GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostDeltaCharacterInertialOrderFifteenExistsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → p % 15 = 1 → SplitsC H.E p → DeltaExists (H := H) p := by
  first | exact @GlobalTheory.Mem.DeltaZero.delta_exists | exact GlobalTheory.Mem.DeltaZero.delta_exists | (intros; apply GlobalTheory.Mem.DeltaZero.delta_exists <;> assumption)
end

