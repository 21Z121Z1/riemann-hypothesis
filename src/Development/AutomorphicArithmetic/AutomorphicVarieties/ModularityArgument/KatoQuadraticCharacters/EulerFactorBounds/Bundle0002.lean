import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0023
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
section
noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem ev_map {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M] (f : M →ₗ[R] M)
    (n : ℕ) (x : AdicCompletion I M) (h : AdicCompletion.eval I M n x = 0) :
    AdicCompletion.eval I M n (AdicCompletion.map I f x) = 0 := by
  change (AdicCompletion.map I f x).val n = 0
  rw [AdicCompletion.map_val_apply]
  change (f.reduceModIdeal (I ^ n)) (AdicCompletion.eval I M n x) = 0
  rw [h, map_zero]

private theorem ev_succ {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    (n : ℕ) (x : AdicCompletion I M) (h : AdicCompletion.eval I M (n + 1) x = 0) :
    AdicCompletion.eval I M n x = 0 := by
  change x.val n = 0
  rw [← x.property (Nat.le_succ n)]
  change (AdicCompletion.transitionMap I M (Nat.le_succ n)) (AdicCompletion.eval I M (n + 1) x) = 0
  rw [h, map_zero]

private theorem ev_zero {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    (x : AdicCompletion I M) : AdicCompletion.eval I M 0 x = 0 := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M 0 x)
  rw [← hy, Submodule.Quotient.mk_eq_zero]
  simp

private theorem ev_smul {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    (n : ℕ) (c : R) (hc : c ∈ I ^ n) (x : AdicCompletion I M) : AdicCompletion.eval I M n (c • x) = 0 := by
  rw [map_smul]
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M n x)
  rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hc Submodule.mem_top

private theorem kmap_comp (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ χ : X.K ≃+* X.K) (h : ∀ f, χ f = ψ (φ f))
    (x : X.Khat l) : X.kmap l χ x = X.kmap l ψ (X.kmap l φ x) := by
  have hl : (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap =
      (MonoidHom.toAdditive (Units.map ψ.toMonoidHom)).toIntLinearMap ∘ₗ
        (MonoidHom.toAdditive (Units.map φ.toMonoidHom)).toIntLinearMap := by
    ext u
    exact h _
  change AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
      (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap) x =
    AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
      (MonoidHom.toAdditive (Units.map ψ.toMonoidHom)).toIntLinearMap)
      (AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
        (MonoidHom.toAdditive (Units.map φ.toMonoidHom)).toIntLinearMap) x)
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp, hl]

private theorem kmap_id (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (χ : X.K ≃+* X.K) (h : ∀ f, χ f = f)
    (x : X.Khat l) : X.kmap l χ x = x := by
  have hl : (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap = LinearMap.id := by
    ext u
    exact h _
  change AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
      (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap) x = x
  rw [hl, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

theorem sApi : SApi := by
  intro Ω _ _ _ ε X l _ n
  refine ⟨⟨fun a u => ?_, fun {a b} hab u => ?_, fun {a b c} hab hbc u => ?_⟩,
    fun a b a' b' h h' => ⟨fun u => ?_, fun u => ?_⟩, fun k a b h u => ?_,
    fun ι S a b h u => ?_, fun k k' a hk => ?_, fun m a b h u => ?_, fun s a b h u => ?_,
    fun a b h u => ev_succ _ _ _ (h u), fun a b u => ev_zero _ _, fun s t a => ?_, fun a => ?_⟩
  · rw [sub_self, map_zero]
  · rw [← neg_sub, map_neg, hab u, neg_zero]
  · rw [← sub_add_sub_cancel (a u) (b u) (c u), map_add, hab u, hbc u, add_zero]
  · rw [Pi.add_apply, Pi.add_apply, add_sub_add_comm, map_add, h u, h' u, add_zero]
  · rw [Pi.sub_apply, Pi.sub_apply, sub_sub_sub_comm, map_sub, h u, h' u, sub_zero]
  · rw [Pi.smul_apply, Pi.smul_apply, ← smul_sub, map_smul, h u, smul_zero]
  · rw [Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib, map_sum]
    exact Finset.sum_eq_zero (fun i hi => h i hi u)
  · rw [← sub_smul]
    apply ev_smul
    rw [idl, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hk
  · simp only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← map_sub]
    exact ev_map (idl l) _ n _ (h _)
  · simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← map_sub]
    exact ev_map (idl l) _ n _ (h _)
  · funext u
    simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    have hst : (s * t).toRingEquiv = s.toRingEquiv * t.toRingEquiv := rfl
    rw [hst, map_mul, Units.val_mul,
      show ((cyclotomicCharacter Ω l) s.toRingEquiv : ℤ_[l]) * ((cyclotomicCharacter Ω l) t.toRingEquiv) * u 1 =
        ((cyclotomicCharacter Ω l) t.toRingEquiv) * (((cyclotomicCharacter Ω l) s.toRingEquiv) * u 1) by ring]
    exact kmap_comp X l _ _ _ (GlobalTheory.K4.gal_mul_apply X s t) _
  · funext u
    simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : (AlgEquiv.toRingEquiv (1 : Gal(Ω/ℚ))) = 1 := rfl
    have hu : ![u 0, u 1] = u := by
      ext i
      fin_cases i <;> rfl
    rw [h1, map_one, Units.val_one, one_mul, hu]
    exact kmap_id X l _ (GlobalTheory.K4.gal_one_apply X) _

end UpperTheory.V.Z.Kato.Nb

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.NatCastNeOfCop
section
noncomputable section

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

def rz (M : ℕ) (a : Fin 2 → ℤ) : Row M := fun i => ((a i : ℤ) : ZMod M)

def aU (l L N : ℕ) (x : ZMod N) : Fin 2 → ℤ := ![(N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L, 0]

def aV (l L N : ℕ) : Fin 2 → ℤ := ![(topT l L N : ℤ) * (l : ℤ) ^ L, (N : ℤ)]

def aUT (l L N p : ℕ) (x : ZMod N) : Fin 2 → ℤ :=
  ![bar l L N p * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L) * p + N * (l : ℤ) ^ L, 0]

def aVT (l L N p : ℕ) : Fin 2 → ℤ :=
  ![bar l L N p * (topT l L N : ℤ) * (l : ℤ) ^ L * p, bar l L N p * N * p + N * (l : ℤ) ^ L]

theorem rz_toQ (M : ℕ) [NeZero M] (a : Fin 2 → ℤ) (i : Fin 2) :
    ∃ j : ℤ, ((a i : ℤ) : ℚ) / (M : ℚ) = toQ M (rz M a) i + j := by
  refine ⟨a i / M, ?_⟩
  have hM : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hv : (((a i : ZMod M).val : ℤ)) = a i % M := ZMod.val_intCast (a i)
  have k : a i % M + M * (a i / M) = a i := by rw [Int.emod_def]; ring
  simp only [toQ, rz]
  rw [div_add' _ _ _ hM, div_left_inj' hM]
  have e : (((a i : ZMod M).val : ℕ) : ℚ) = ((a i % M : ℤ) : ℚ) := by exact_mod_cast hv
  rw [e]
  have k' : ((a i % M + M * (a i / M) : ℤ) : ℚ) = ((a i : ℤ) : ℚ) := by exact_mod_cast k
  push_cast at k' ⊢
  linarith

theorem rz_congr {M : ℕ} {a b : Fin 2 → ℤ} (h : ∀ i, (M : ℤ) ∣ b i - a i) : rz M a = rz M b := by
  funext i
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (h i)

theorem smul_rz (M : ℕ) (k : ℤ) (a : Fin 2 → ℤ) : (k : ZMod M) • rz M a = rz M (k • a) := by
  funext i
  simp [rz]

theorem up_rz (k M : ℕ) [NeZero M] (a : Fin 2 → ℤ) : up k M (rz M a) = rz (k * M) ((k : ℤ) • a) := by
  funext i
  simp only [up, rz, Pi.smul_apply, smul_eq_mul]
  have hv : (((a i : ZMod M).val : ℤ)) = a i % M := ZMod.val_intCast (a i)
  rw [show ((k * (a i : ZMod M).val : ℕ) : ZMod (k * M)) = (((k * (a i % M) : ℤ)) : ZMod (k * M)) by
    rw [← hv]; push_cast; rfl]
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2
  refine ⟨a i / M, ?_⟩
  have k' : a i % M + M * (a i / M) = a i := by rw [Int.emod_def]; ring
  push_cast
  linear_combination (-(k : ℤ)) * k'

theorem two_smul_rz_ne {M l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (h : l ∣ M) (a : Fin 2 → ℤ) (i : Fin 2)
    (ha : ((a i : ℤ) : ZMod l) ≠ 0) : (2 : ZMod M) • rz M a ≠ 0 := by
  haveI := Fact.mk hl
  intro hz
  have h' := congrFun hz i
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, rz] at h'
  have h'' := congrArg (ZMod.castHom h (ZMod l)) h'
  rw [map_mul, map_intCast, map_zero, map_ofNat] at h''
  rcases mul_eq_zero.1 h'' with h2' | h2'
  · have h3 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h2'
    have h4 := (CharP.cast_eq_zero_iff (ZMod l) l 2).1 h3
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h4)
  · exact ha h2'

theorem natCast_ne_of_cop {l N : ℕ} (hl : l.Prime) (hc : Nat.Coprime l N) : (N : ZMod l) ≠ 0 := by
  intro h0
  have hd := (CharP.cast_eq_zero_iff (ZMod l) l N).1 h0
  exact hl.ne_one (Nat.Coprime.eq_one_of_dvd hc hd)

theorem bar_mul {l N p : ℕ} (L : ℕ) (hl : l ≠ 0) (hN : N ≠ 0) (hp : Nat.Coprime p (l * N)) :
    ((N * l ^ L : ℕ) : ℤ) ∣ bar l L N p * p - 1 := by
  have h1 : Nat.Coprime p l := Nat.Coprime.coprime_dvd_right (dvd_mul_right l N) hp
  have h2 : Nat.Coprime p N := Nat.Coprime.coprime_dvd_right (dvd_mul_left N l) hp
  have hcop : Nat.Coprime p (N * l ^ L) := Nat.Coprime.mul_right h2 (Nat.Coprime.pow_right L h1)
  haveI : NeZero (N * l ^ L) := ⟨mul_ne_zero hN (pow_ne_zero _ hl)⟩
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub 1 _ _).1
  unfold bar
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact (ZMod.coe_mul_inv_eq_one p hcop).symm.trans (mul_comm _ _)

theorem bar_mul_l {l N p L : ℕ} (hL : 1 ≤ L) (hl : l ≠ 0) (hN : N ≠ 0) (hp : Nat.Coprime p (l * N)) :
    ((bar l L N p : ℤ) : ZMod l) * (p : ZMod l) = 1 := by
  have h6 := bar_mul L hl hN hp
  have hl' : (l : ℤ) ∣ ((N * l ^ L : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.2 (Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N)
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (bar l L N p * p) l).2 (dvd_trans hl' h6)
  push_cast at hd
  exact hd.symm

theorem aU_mod {l L N : ℕ} (hL : 1 ≤ L) (x : ZMod N) :
    ((aU l L N x 0 : ℤ) : ZMod l) = N ∧ ((aU l L N x 1 : ℤ) : ZMod l) = 0 := by
  constructor
  · simp only [aU, Matrix.cons_val_zero]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega), mul_zero, add_zero]
  · simp [aU]

theorem aV_mod {l L N : ℕ} (hL : 1 ≤ L) :
    ((aV l L N 0 : ℤ) : ZMod l) = 0 ∧ ((aV l L N 1 : ℤ) : ZMod l) = N := by
  constructor
  · simp only [aV, Matrix.cons_val_zero]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega), mul_zero]
  · simp [aV]

theorem aUT_mod {l L N p : ℕ} (hL : 1 ≤ L) (hl : l ≠ 0) (hN : N ≠ 0) (hp : Nat.Coprime p (l * N)) (x : ZMod N) :
    ((aUT l L N p x 0 : ℤ) : ZMod l) = N ∧ ((aUT l L N p x 1 : ℤ) : ZMod l) = 0 := by
  have hb := bar_mul_l hL hl hN hp
  constructor
  · simp only [aUT, Matrix.cons_val_zero]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega)]
    linear_combination (N : ZMod l) * hb
  · simp [aUT]

theorem aVT_mod {l L N p : ℕ} (hL : 1 ≤ L) (hl : l ≠ 0) (hN : N ≠ 0) (hp : Nat.Coprime p (l * N)) :
    ((aVT l L N p 0 : ℤ) : ZMod l) = 0 ∧ ((aVT l L N p 1 : ℤ) : ZMod l) = N := by
  have hb := bar_mul_l hL hl hN hp
  constructor
  · simp only [aVT, Matrix.cons_val_zero]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega)]
    ring
  · simp only [aVT, Matrix.cons_val_one, Matrix.head_cons]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega)]
    linear_combination (N : ZMod l) * hb

theorem ok_of_mod {M l N : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (hc : Nat.Coprime l N) (h : l ∣ M) {a b : Fin 2 → ℤ}
    (ha : ((a 0 : ℤ) : ZMod l) = N) (hb : ((b 1 : ℤ) : ZMod l) = N) : Ok (rz M a) (rz M b) := by
  refine ⟨?_, ?_⟩
  · have hne := two_smul_rz_ne hl h2 h a 0 (by rw [ha]; exact natCast_ne_of_cop hl hc)
    intro hz
    apply hne
    funext j
    have hj := congrFun hz j
    simp only [Pi.smul_apply, Pi.zero_apply] at hj ⊢
    simpa [two_nsmul, two_zsmul, two_smul] using hj
  · have hne := two_smul_rz_ne hl h2 h b 1 (by rw [hb]; exact natCast_ne_of_cop hl hc)
    intro hz
    apply hne
    funext j
    have hj := congrFun hz j
    simp only [Pi.smul_apply, Pi.zero_apply] at hj ⊢
    simpa [two_nsmul, two_zsmul, two_smul] using hj

theorem ok_UV {M l L N : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (hc : Nat.Coprime l N) (hL : 1 ≤ L) (h : l ∣ M) (x : ZMod N) :
    Ok (rz M (aU l L N x)) (rz M (aV l L N)) :=
  ok_of_mod hl h2 hc h (aU_mod hL x).1 (aV_mod hL).2

theorem ok_UVT {M l L N p : ℕ} [NeZero N] (hl : l.Prime) (h2 : l ≠ 2) (hc : Nat.Coprime l N) (hL : 1 ≤ L) (h : l ∣ M)
    (hp : Nat.Coprime p (l * N)) (x : ZMod N) : Ok (rz M (aUT l L N p x)) (rz M (aVT l L N p)) :=
  ok_of_mod hl h2 hc h (aUT_mod hL hl.ne_zero (NeZero.ne N) hp x).1 (aVT_mod hL hl.ne_zero (NeZero.ne N) hp).2

theorem ixU_toQ {M l L N : ℕ} [NeZero M] (hM : M = N * l ^ L) (x : ZMod N) (i : Fin 2) :
    ∃ j : ℤ, ixU l L N x i = toQ M (rz M (aU l L N x)) i + j := by
  subst hM
  obtain ⟨j, hj⟩ := rz_toQ (N * l ^ L) (aU l L N x) i
  refine ⟨j, ?_⟩
  rw [← hj]
  fin_cases i <;> rfl

theorem ixV_toQ {M l L N : ℕ} [NeZero M] (hM : M = N * l ^ L) (i : Fin 2) :
    ∃ j : ℤ, ixV l L N i = toQ M (rz M (aV l L N)) i + j := by
  subst hM
  obtain ⟨j, hj⟩ := rz_toQ (N * l ^ L) (aV l L N) i
  refine ⟨j, ?_⟩
  rw [← hj]
  fin_cases i <;> rfl

theorem ixUT_toQ {M l L N p : ℕ} [NeZero M] (hM : M = N * l ^ L * p) (x : ZMod N) (i : Fin 2) :
    ∃ j : ℤ, ixUT l L N p x i = toQ M (rz M (aUT l L N p x)) i + j := by
  subst hM
  obtain ⟨j, hj⟩ := rz_toQ (N * l ^ L * p) (aUT l L N p x) i
  refine ⟨j, ?_⟩
  rw [← hj]
  fin_cases i <;> rfl

theorem ixVT_toQ {M l L N p : ℕ} [NeZero M] (hM : M = N * l ^ L * p) (i : Fin 2) :
    ∃ j : ℤ, ixVT l L N p i = toQ M (rz M (aVT l L N p)) i + j := by
  subst hM
  obtain ⟨j, hj⟩ := rz_toQ (N * l ^ L * p) (aVT l L N p) i
  refine ⟨j, ?_⟩
  rw [← hj]
  fin_cases i <;> rfl

theorem Hyp.lv {l N c d : ℕ} {g : SL(2, ℤ)} (H : Hyp l N c d g) (hl : l ≠ 0) (hN : N ≠ 0) {M L : ℕ} (hM : M = N * l ^ L) :
    Lv c d M := by
  subst hM
  refine ⟨Nat.pos_of_ne_zero (mul_ne_zero hN (pow_ne_zero _ hl)), ?_, ?_⟩
  · have h1 : c.Coprime l := Nat.Coprime.coprime_dvd_right (Dvd.intro (6 * N) (by ring)) H.cc
    have h2 : c.Coprime N := Nat.Coprime.coprime_dvd_right (Dvd.intro_left (6 * l) rfl) H.cc
    exact Nat.Coprime.mul_right h2 (Nat.Coprime.pow_right L h1)
  · have h1 : d.Coprime l := Nat.Coprime.coprime_dvd_right (Dvd.intro (6 * N) (by ring)) H.cd
    have h2 : d.Coprime N := Nat.Coprime.coprime_dvd_right (Dvd.intro_left (6 * l) rfl) H.cd
    exact Nat.Coprime.mul_right h2 (Nat.Coprime.pow_right L h1)

theorem Hyp.lvT {l N c d p : ℕ} {g : SL(2, ℤ)} (H : Hyp l N c d g) (hl : l ≠ 0) (hN : N ≠ 0) (hp0 : p ≠ 0)
    (hp : Nat.Coprime p (l * N * c * d)) {M L : ℕ} (hM : M = N * l ^ L * p) : Lv c d M := by
  subst hM
  obtain ⟨h0, h1, h2⟩ := H.lv hl hN (rfl : N * l ^ L = N * l ^ L)
  exact ⟨Nat.mul_pos h0 (Nat.pos_of_ne_zero hp0),
    h1.mul_right (Nat.Coprime.coprime_mul_left_right (Nat.Coprime.coprime_mul_right_right hp)).symm,
    h2.mul_right (Nat.Coprime.coprime_mul_left_right hp).symm⟩

end UpperTheory.V.Z.Kato.Nb

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb

def Rel {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l)
    (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l) (N : ℕ) (cf : Coef l) (c n : ℕ) {T : Type} [Mul T] (κ : (Ω ≃ₐ[ℚ] Ω) → T)
    (Y : (Ω ≃ₐ[ℚ] Ω) → T → Fin 2 → Qbar l) (z : (Ω ≃ₐ[ℚ] Ω) → T → X.Fn l) : Prop :=
  ∃ (β : (Ω ≃ₐ[ℚ] Ω) → T → X.Fn l) (b : T → Fin 2 → Qbar l), (∀ s y, LiftB X l N (2 * e - 1) n c (z s y) (β s y)) ∧
    (∀ y i, b y i ∈ cf.O) ∧ ∀ s y, Cv n (Y s y) (pr (β s y) + (rhoK W e ψ s *ᵥ b (y * κ s) - b y))

def eul (l : ℕ) [Fact l.Prime] (e p : ℕ) (a δ : Qbar l) : Qbar l := 1 - a * ((p : Qbar l) ^ (e + 1))⁻¹ + δ * ((p : Qbar l) ^ 2)⁻¹

def SRel0 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → ∀ (c₀ : ℕ) Y, IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y → ∀ r n : ℕ,
    Rel X l pr W e ψ N cf c₀ n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) (Y r) fun s y => ∑ r₀, Y0 X l n r N x c d (2 * e - 1) (gm r₀) s y

def SRelT : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → ∀ (p : ℕ) [NeZero p], Nat.Coprime p l → ∀ (c₀ : ℕ) Y, IsZTc X l pr W e ψ N p x c d (2 * e + 1) gm cf c₀ Y → ∀ r n : ℕ,
    Rel X l pr W e ψ N cf c₀ n (kT l r p) (Y r) fun s y => ∑ r₀, YT X l n r N p x c d (2 * e - 1) (gm r₀) s y

def SN2rho : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → (∀ s i k, mat W s i k ∈ cf.O) → ∃ m : ℕ, ∀ (p : ℕ) [NeZero p], p.Prime → Nat.Coprime p (l * N) → ∀ a δ : Qbar l, a ∈ cf.O → δ ∈ cf.O →
    (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeT N l p b) = a • pr b ∧ pr (X.diam N l p b) = δ • pr b) →
    ∀ (c₀ c₁ r n : ℕ) (Y : (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (Y' : (Ω ≃ₐ[ℚ] Ω) → (ZMod p)ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) z z',
      Rel X l pr W e ψ N cf c₀ n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) Y z → Rel X l pr W e ψ N cf (c₀ + c₁) n (kT l r p) Y' z' →
      CohB X l N (2 * e - 1) n (fun s => (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) (fun s y => (p : ℤ_[l]) • ∑ t, z' s (t, y))
        (fun s y => (p : ℤ_[l]) • z s y - X.heckeT N l p (z s (y * inv1 (l ^ r) p)) +
          (p : ℤ_[l]) ^ (2 * e - 1) • X.diam N l p (z s (y * inv1 (l ^ r) p ^ 2))) →
      ∃ b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
        Cv n ((((l : ℕ) : Qbar l) ^ m * (p : Qbar l)) • ∑ t, Y' s (t, y))
          (((l : ℕ) : Qbar l) ^ (m + c₁) • ((p : Qbar l) • Y s y - a • Y s (y * inv1 (l ^ r) p) +
            ((p : Qbar l) ^ (2 * e - 1) * δ) • Y s (y * inv1 (l ^ r) p ^ 2)) +
            (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))

def SInteg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → (∀ s i k, mat W s i k ∈ cf.O) → (∀ s : G ℚ Ω, ‖thK l e ψ s‖ = 1) ∧ ψ 1 = 1 ∧ (∀ u v : (ZMod l)ˣ, ψ ((u * v : (ZMod l)ˣ) : ZMod l) = ψ u * ψ v) ∧
    (∀ u : (ZMod l)ˣ, ψ u ∈ cf.O) ∧ (∀ s i k, rhoK W e ψ s i k ∈ cf.O) ∧ (∀ s t, rhoK W e ψ (s * t) = rhoK W e ψ s * rhoK W e ψ t) ∧
    ∀ (c₀ : ℕ) Y, IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y → ∀ r s y i, ‖Y r s y i‖ ≤ 1

def SSpec : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → (∀ s i k, mat W s i k ∈ cf.O) → ∀ (p r : ℕ), p.Prime → l ∣ p - 1 → ∀ (a δ k : Qbar l), ‖a‖ ≤ 1 → ‖δ‖ ≤ 1 → ‖k‖ ≤ 1 →
    ∀ (Y V : (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l), (∀ s y i, ‖Y s y i‖ ≤ 1) → (∀ y i, b y i ∈ cf.O) →
      (∀ s y, Cv r ((p : Qbar l) • V s y) (k • ((p : Qbar l) • Y s y - a • Y s (y * inv1 (l ^ r) p) +
          ((p : Qbar l) ^ (2 * e - 1) * δ) • Y s (y * inv1 (l ^ r) p ^ 2)) +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))) →
      ∃ b' : Fin 2 → Qbar l, (∀ i, b' i ∈ cf.O) ∧ ∀ s, Cv r (spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) V s)
        (eul l e p a δ • (k • spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) Y s) + (mat W s *ᵥ b' - b'))

def SDetChar : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (χ : G ℚ Ω →* (Qbar l)ˣ),
    Continuous ρ → Continuous χ → (∃ s, ∀ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) ≠ t • 1) → ∀ S : Finset ℕ,
    (∀ (v : Pl) (B : ValuationSubring Ω) (σ : G ℚ Ω), normV v ∉ S → IsPlaceOver B v → IsFrob B (normV v) σ → ∃ a : Qbar l,
      (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)) ^ 2 - a • (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)) + (χ σ : Qbar l) • 1 = 0) →
    ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = χ s

def SDiamChar : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → Nat.Coprime l N → (∃ b ∈ X.B N l (2 * e - 1), pr b ≠ 0) → ∃ δ : (ZMod N)ˣ →* (Qbar l)ˣ, ∀ (q : ℕ) (u : (ZMod N)ˣ), q.Prime → ¬ q ∣ l * N →
    (u : ZMod N) = q → ∀ b ∈ X.B N l (2 * e - 1), pr (X.diam N l q b) = (δ u : Qbar l) • pr b

def SEuler : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → Nat.Coprime l N → ∀ S : Finset Pl, Nf e S A W → (∀ s i k, mat W s i k ∈ cf.O) → ∃ S' : Finset Pl, S ⊆ S' ∧ ∀ w : Pl, w ∉ S' →
    (normV w).Prime ∧ Nat.Coprime (normV w) (l * N * c * d) ∧ ∃ a δ : Qbar l, a ∈ cf.O ∧ δ ∈ cf.O ∧
      (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeT N l (normV w) b) = a • pr b ∧ pr (X.diam N l (normV w) b) = δ • pr b) ∧
      ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ →
        eps l σ = (normV w : Qbar l) ∧ (rhoK W e ψ σ).trace = a ∧ (rhoK W e ψ σ).det = (normV w : Qbar l) ^ (2 * e) * δ

def SEulCg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → 1 ≤ e → ∀ (p n : ℕ), p.Prime → 1 ≤ n → l ^ n ∣ p - 1 → ∀ a δ : Qbar l, a ∈ cf.O → δ ∈ cf.O → eul l e p a δ ∈ cf.O ∧
    ∀ σ : G ℚ Ω, ψ 1 = 1 → eps l σ = (p : Qbar l) → (rhoK W e ψ σ).trace = a → (rhoK W e ψ σ).det = (p : Qbar l) ^ (2 * e) * δ →
      Cg n (eul l e p a δ) (1 * (mat W σ - 1).det)

def SPushPsi : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (cf : Coef l) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (p n : ℕ) [NeZero p] (ψw : G ℚ Ω →* Multiplicative (ZMod (l ^ n))), KillsMu p ψw →
    ∀ Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod p)ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
      (∀ r s s' y, Y r (s * s') y = Y r s y + ρ s *ᵥ Y r s' (y * cycT l r p s)) →
      (∀ r, Y r = GlobalTheory.KA.push (Prod.map id (redL l r)) (Y (r + 1))) → (∀ r y i, Continuous fun s => Y r s y i) → (∀ r s u i, Y r s u i ∈ cf.O) →
      ∃ Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
        (∀ r, ShCoc ρ (ψw.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) ∧ (∀ r x i, Continuous fun s => Yw r s x i) ∧ (∀ r s x i, Yw r s x i ∈ cf.O) ∧
        (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) ∧
        ∀ r s y, ∑ a, Yw r s (a, y) = ∑ t, Y r s (t, y)

def KatoTameRelationProjected : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
  (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
  (ψ : ZMod l → Qbar l) (cf : Coef l) (S : Finset Pl),
  Nf e S A W → (∀ s i k, mat W s i k ∈ cf.O) → (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e → (∃ x, cw x ≠ 0) →
  (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → AdmWn ι e gN A W X pr N cw c d gm ψ cf →
  ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l), IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y →
  ∃ (k : ℕ) (S' : Finset Pl), (∀ w : Pl, w ∉ S' → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) ∧
  ∀ n : ℕ, 1 ≤ n → ∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψw : G ℚ Ω →* Multiplicative (ZMod (l ^ n)),
    KillsMu (normV w) ψw → Function.Surjective ψw →
    ∃ (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (P u : Qbar l)
      (b : ℕ → Fin 2 → Qbar l),
      (∀ r, ShCoc (rhoK W e ψ) (ψw.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) ∧ (∀ r x i, Continuous fun s => Yw r s x i) ∧
      (∀ r s x i, Yw r s x i ∈ cf.O) ∧
      (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) ∧
      P ∈ cf.O ∧ ‖u‖ = 1 ∧ (∀ r i, b r i ∈ cf.O) ∧
      (∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) (fun s x => Yw r s (a, x)) s) i -
          (P • (((l : ℕ) : Qbar l) ^ k • spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x) (Y r) s) + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
      (∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ → Cg n P (u * (mat W σ - 1).det))

end UpperTheory.V.Z.Kato.Nb

end
end

