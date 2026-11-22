import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDirData
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem sq_neg_one {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) :
    χ ((-1 : ℤ) : ZMod N) ^ 2 = 1 := by
  have h : ((-1 : ℤ) : ZMod N) ^ 2 = 1 := by
    push_cast
    exact neg_one_sq
  first
    | rw [← map_pow, h, map_one]
    | rw [sq, ← χ.map_mul, ← sq, h, χ.map_one]

private theorem pow_app {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (k : ℕ) (a : ℤ)
    (ha : IsCoprime a (N : ℤ)) : (χ ^ k) (a : ZMod N) = χ a ^ k := by
  obtain ⟨u, v, huv⟩ := ha
  have h := congrArg (fun x : ℤ => (x : ZMod N)) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero,
    Int.cast_one] at h
  rw [← show ((⟨_, _, (mul_comm _ _).trans h, h⟩ : (ZMod N)ˣ) : ZMod N) = ((a : ℤ) : ZMod N) from rfl]
  exact MulChar.pow_apply_coe χ k _

theorem UpperTheory.V.X.dirData :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ → ∀ q : ℕ, UnitaryThreeInertia.XData l ψ q → ∀ ω : DirichletCharacter c.O l, ω ^ (l - 1) = 1 → ∃ (d f n : ℕ) (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)), XData l d φ ξ ∧ f * 2 ^ n ∣ l * N * N ∧ ∀ a : ℤ, IsCoprime a (l * N * N : ℕ) → prodX φ ξ a = (ω a ^ e * psi2 ψ a * th1 l ψ a) ^ 2 * ((ZMod.χ₄ a : ℤ) : c.O) := by
  intro l hl c N iN e ψ o₁ hD q hX ω hω
  have hl2 : l ≠ 2 := hD.l_odd
  have h4l : 4 ≤ c2 ψ := hD.four_le
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨hq0, hq, hb⟩ := hX
  obtain ⟨-, -, hcod, hf0, hfour, hth, hl1⟩ := UpperTheory.V.X.th1Facts c.O N ψ l hl.out hl2
  obtain ⟨-, -, -, h2c, h2N, -⟩ := UpperTheory.V.HV.compCond c.O N ψ 2 Nat.prime_two
  obtain ⟨ξ, hξp, hξ⟩ :=
    UpperTheory.V.X.xiSq c.O two_ne_zero N (psi2 ψ) (c2 ψ) h4l h2c.symm
  obtain ⟨f, φ, hφp, hfd, hφo, hφ⟩ :=
    UpperTheory.V.X.primProd c.O l N ((ω ^ e) ^ 2) (th1 l ψ ^ 2)
  have hdiv : f * 2 ^ (c2 ψ - 1) ∣ l * N * N :=
    mul_dvd_mul (dvd_trans hfd (mul_dvd_mul_left l (DirichletCharacter.conductor_dvd_level _)))
      (dvd_trans (pow_dvd_pow 2 (Nat.sub_le _ 1)) h2N)
  have unitOf : ∀ (m : ℕ) (a : ℤ), IsCoprime a (m : ℤ) → IsUnit ((a : ZMod m)) := by
    rintro m a ⟨u, v, huv⟩
    have h := congrArg (fun x : ℤ => (x : ZMod m)) huv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero,
      Int.cast_one] at h
    exact ⟨⟨_, _, (mul_comm _ _).trans h, h⟩, rfl⟩
  refine ⟨f0 l ψ, f, c2 ψ - 1, φ, ξ, ?_, hdiv, ?_⟩
  · have hT : ((ω ^ e) ^ 2) ^ (l ^ f0 l ψ - 1) = 1 := by
      obtain ⟨t, ht⟩ := hl1
      calc ((ω ^ e) ^ 2) ^ (l ^ f0 l ψ - 1) = (ω ^ (l - 1)) ^ (e * 2 * t) := by
            rw [ht, ← pow_mul, ← pow_mul, ← pow_mul]
            congr 1
            ring
        _ = 1 := by rw [hω, one_pow]
    have hT2 : (th1 l ψ ^ 2) ^ (l ^ f0 l ψ - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hth, one_pow]
    refine ⟨hf0, hfour, ?_, hφp, orderOf_dvd_of_pow_eq_one (hφo _ hT hT2), hξp, ?_, ?_⟩
    · exact Odd.of_dvd_nat ((hl.out.odd_of_ne_two hl2).mul hcod) hfd
    · have hfle : f ≤ l * q :=
        Nat.le_of_dvd (Nat.mul_pos hl.out.pos hq0) (dvd_trans hfd (mul_dvd_mul_left l hq))
      have h2 : 2 ^ c2 ψ = 2 * 2 ^ (c2 ψ - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hb' : 2 * (l * q * 4 ^ (l ^ f0 l ψ - 1).factorization 2) ≤ 2 * 2 ^ (c2 ψ - 1) := by
        rw [← mul_assoc, ← h2]
        exact hb
      exact le_trans (Nat.mul_le_mul_right _ hfle) (Nat.le_of_mul_le_mul_left hb' two_pos)
    · have hc1 : IsCoprime (-1 : ℤ) ((l * N : ℕ) : ℤ) := isCoprime_one_left.neg_left
      have hc2 : IsCoprime (-1 : ℤ) (N : ℤ) := isCoprime_one_left.neg_left
      have hm1 : IsCoprime (-1 : ℤ) (l : ℤ) := isCoprime_one_left.neg_left
      have e1 := hφ (-1) hc1
      have e2 := hξ (-1) hc2
      rw [pow_app _ _ _ hm1, pow_app _ _ _ hm1, pow_app _ _ _ hc2] at e1
      have hw : (ω ((-1 : ℤ) : ZMod l) ^ e) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, sq_neg_one, one_pow]
      rw [hw, sq_neg_one, one_mul] at e1
      rw [sq_neg_one, one_mul] at e2
      have h4 : ZMod.χ₄ ((-1 : ℤ) : ZMod 4) = -1 := by
        first
          | decide
          | rfl
          | simp
      have n1 : (-1 : ZMod f) = ((-1 : ℤ) : ZMod f) := by simp
      have n2 : (-1 : ZMod (2 ^ (c2 ψ - 1))) = ((-1 : ℤ) : ZMod (2 ^ (c2 ψ - 1))) := by simp
      rw [n1, n2, e1, e2, h4]
      simp
  · intro a ha
    have haN : IsCoprime a (N : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 (dvd_mul_left N (l * N)))
    have halN : IsCoprime a ((l * N : ℕ) : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 (dvd_mul_right (l * N) N))
    have hal : IsCoprime a (l : ℤ) :=
      ha.of_isCoprime_of_dvd_right
        (Int.natCast_dvd_natCast.2 (dvd_trans (dvd_mul_right l N) (dvd_mul_right (l * N) N)))
    have had : IsCoprime a ((f * 2 ^ (c2 ψ - 1) : ℕ) : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hdiv)
    obtain ⟨u, hu⟩ := unitOf _ a had
    rw [UpperTheory.V.X.prodX, MulChar.coeToFun_mul, Pi.mul_apply, ← hu,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
      ZMod.cast_intCast (R := ZMod f) (Dvd.intro _ rfl : f ∣ f * 2 ^ (c2 ψ - 1)) a,
      ZMod.cast_intCast (R := ZMod (2 ^ (c2 ψ - 1)))
        (Dvd.intro_left _ rfl : 2 ^ (c2 ψ - 1) ∣ f * 2 ^ (c2 ψ - 1)) a,
      hφ a halN, hξ a haN, pow_app _ _ _ hal, pow_app _ _ _ hal, pow_app _ _ _ haN]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcXppOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

section SlopeTestRemainingChoices
open UpperTheory.V.U3 UpperTheory.V.UnitaryThreeInertia

private def eGb {k : Type} [CommRing k] (a : k) : Gb k (-2) :=
  (⟨Matrix.single 2 0 a, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert h; decide) | simp⟩ : gw k (-2))

private theorem eGb_val {k : Type} [CommRing k] (a : k) : (eGb a).val 2 0 = a := by
  show Matrix.single 2 0 a 2 0 = a
  exact Matrix.single_apply_same _ _ _

private theorem gb_ext {k : Type} [CommRing k] {X Y : Gb k (-2)} (h : X.val 2 0 = Y.val 2 0) : X = Y := by
  have hX : ∀ a b, UpperTheory.V.U3.wt a b ≠ -2 → (X.val : Matrix (Fin 3) (Fin 3) k) a b = 0 := X.2
  have hY : ∀ a b, UpperTheory.V.U3.wt a b ≠ -2 → (Y.val : Matrix (Fin 3) (Fin 3) k) a b = 0 := Y.2
  apply Subtype.ext
  ext a b
  by_cases hab : a = 2 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    exact h
  · have hw : UpperTheory.V.U3.wt a b ≠ -2 := by
      revert hab
      fin_cases a <;> fin_cases b <;> first | decide | simp [UpperTheory.V.U3.wt, UpperTheory.V.U3.wt1]
    exact (hX a b hw).trans (hY a b hw).symm

private theorem gb_add {k : Type} [CommRing k] (X Y : Gb k (-2)) : (X + Y).val 2 0 = X.val 2 0 + Y.val 2 0 := rfl
private theorem gb_sub {k : Type} [CommRing k] (X Y : Gb k (-2)) : (X - Y).val 2 0 = X.val 2 0 - Y.val 2 0 := rfl

private theorem gb_rep {k D : Type} [CommRing k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) (g : D) (X : Gb k (-2))
    (c : k) (hc : c * (Ψ g : k) ^ 2 = ((η g : ℤ) : k)) :
    (gRep η Ψ (-2) g X).val 2 0 = c * X.val 2 0 := by
  rw [gRep_val, adRep_baseLift_apply]
  have hw : UpperTheory.V.U3.wt 2 0 = -2 := by decide
  have r0 : Fin.rev (0 : Fin 3) = 2 := rfl
  have r2 : Fin.rev (2 : Fin 3) = 0 := rfl
  rw [hw, r0, r2, zpow_neg, zpow_ofNat]
  have hc' : c = ((η g : ℤ) : k) * (((Ψ g ^ 2)⁻¹ : kˣ) : k) := by
    have h0 : c * (((Ψ g ^ 2 : kˣ)) : k) * (((Ψ g ^ 2)⁻¹ : kˣ) : k) = c :=
      Units.mul_inv_cancel_right _ _
    rw [Units.val_pow_eq_pow_val, hc] at h0
    exact h0.symm
  rw [hc']
  rcases Int.units_eq_one_or (η g) with h1 | h1
  · rw [if_pos h1, h1]
    simp only [Units.val_one, Int.cast_one]
    ring
  · rw [if_neg (by rw [h1]; decide), h1]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.X.xppOf :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G' Γ ι : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [Group Γ] [TopologicalSpace Γ] (F : UnitaryThreeInertia.Frame O G' Γ ι) (γ : Γ → ResidueField O), (∀ g, γ g * (F.Ψbar g : ResidueField O) ^ 2 = ((F.η g : ℤ) : ResidueField O)) → (∀ z : Γ → ResidueField O, IsLocallyConstant z → (∀ g h, z (g * h) = z g + γ g * z h) → (∀ v, v ≠ F.vl → ∀ s ∈ F.Nv v, z (F.loc v s) = 0) → (∃ m, ∀ s, z (F.loc F.vl s) = γ (F.loc F.vl s) * m - m) → ∃ m, ∀ g, z g = γ g * m - m) → F.Xpp := by
  intro O iR iL G' Γ ι iG iT iTG iΓ iTΓ F γ hγ hmain
  show Subsingleton (F.selmerCohomologyQuotient (-2))
  refine Submodule.Quotient.subsingleton_iff.2 ?_
  rw [eq_top_iff]
  rintro ⟨f, hf⟩ -
  show f ∈ B1 (F.gbar (-2))
  obtain ⟨hZ, hL⟩ := Submodule.mem_inf.1 hf
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 hZ
  have hZL : ∀ v, F.res1 (-2) v f ∈ Z1 (F.gloc (-2) v) ∧
      (v ≠ F.vl → ∀ s ∈ F.Nv v, F.res1 (-2) v f s = 0) ∧
      (v = F.vl → (-2 : ℤ) < 0 → F.res1 (-2) v f ∈ B1 (F.gloc (-2) v)) ∧
      (v = F.vl → (-2 : ℤ) = 0 → ∀ s ∈ F.Iv v, F.res1 (-2) v f s = 0) :=
    fun v => (Submodule.mem_iInf _).1 hL v
  have hlc : IsLocallyConstant (fun g => (f g).val 2 0) :=
    ((IsLocallyConstant.iff_continuous _).2 hcont).comp
      (fun X : UpperTheory.V.UnitaryThreeInertia.Gb (ResidueField O) (-2) => X.val 2 0)
  obtain ⟨m, hm⟩ := hmain (fun g => (f g).val 2 0) hlc
    (by
      intro g h
      show (f (g * h)).val 2 0 = (f g).val 2 0 + γ g * (f h).val 2 0
      rw [hcoc g h, gb_add, gb_rep F.η F.Ψbar g _ (γ g) (hγ g)])
    (by
      intro v hv s hs
      have h0 : f (F.loc v s) = 0 := (hZL v).2.1 hv s hs
      show (f (F.loc v s)).val 2 0 = 0
      rw [h0]
      rfl)
    (by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((hZL F.vl).2.2.1 rfl (by norm_num))
      refine ⟨m.val 2 0, fun s => ?_⟩
      have h' : f (F.loc F.vl s) = F.gbar (-2) (F.loc F.vl s) m - m := hm s
      show (f (F.loc F.vl s)).val 2 0 = _
      rw [h', gb_sub, gb_rep F.η F.Ψbar _ _ (γ _) (hγ _)])
  rw [mem_coboundaries1]
  refine ⟨eGb m, fun g => gb_ext ?_⟩
  rw [gb_sub, gb_rep F.η F.Ψbar g _ (γ g) (hγ g), eGb_val]
  exact hm g
end

