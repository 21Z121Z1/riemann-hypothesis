import Mathlib

-- bundled from Formalism.PeriodIntegrals.UnimodLocStd
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace PI.ULS

abbrev Sesq (V : Type*) [AddCommGroup V] [Module ℂ V] := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def altE (H : Sesq V) (x y : V) : ℝ := (H x y).im

def dualLat (H : Sesq V) (Λ : AddSubgroup V) : AddSubgroup V where
  carrier := {x | ∀ y ∈ Λ, ∃ m : ℤ, altE H x y = (m : ℝ)}
  zero_mem' := fun y _ => ⟨0, by simp [altE]⟩
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨m, hm⟩ := ha y hy
    obtain ⟨k, hk⟩ := hb y hy
    exact ⟨m + k, by simp only [altE] at hm hk ⊢; simp [hm, hk]⟩
  neg_mem' := by
    intro a ha y hy
    obtain ⟨m, hm⟩ := ha y hy
    exact ⟨-m, by simp only [altE] at hm ⊢; simp [hm]⟩

def IsSelfDual (H : Sesq V) (Λ : AddSubgroup V) : Prop := dualLat H Λ = Λ

def relIdx (Λ₁ Λ₂ : AddSubgroup V) : ℕ := Λ₁.relIndex Λ₂

def IsIsom {W : Type*} [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W) (g : V →ₗ[ℂ] W) : Prop :=
  ∀ x y, H' (g x) (g y) = H x y

def imgLat {W : Type*} [AddCommGroup W] [Module ℂ W] (g : V →ₗ[ℂ] W) (Λ : AddSubgroup V) : AddSubgroup W :=
  Λ.map g.toAddMonoidHom

end General

def area (L : PeriodPair) : ℝ := |(conj L.ω₁ * L.ω₂).im|

section Coordinates

variable {n : Type*} [Fintype n]

def matH (h : Matrix n n ℂ) : Sesq (n → ℂ) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => ∑ i, ∑ j, z i * h i j * conj (w j))
    (by intro a b c; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (by intro c a b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc])
    (by intro a b c; simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)

def stdH (L : PeriodPair) (n : Type*) [Fintype n] [DecidableEq n] : Sesq (n → ℂ) :=
  matH (((area L : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ))

def stdLat (L : PeriodPair) (n : Type*) : AddSubgroup (n → ℂ) :=
  AddSubgroup.pi Set.univ fun _ => L.lattice.toAddSubgroup

end Coordinates

def scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have h := L.indep
    rw [LinearIndependent.pair_iff] at h ⊢
    intro s t hst
    apply h s t
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.mp this).resolve_left hc

def cmTheta (b : ℤ) (d : ℕ) : ℂ := ((b : ℂ) + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2

def cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) : PeriodPair where
  ω₁ := (a : ℂ)
  ω₂ := cmTheta b d
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [cmTheta] at him hre
    have ht : t = 0 := by
      rcases him with h1 | h1
      · exact h1
      · exact absurd h1 (by positivity)
    subst ht
    simp at hre
    refine ⟨?_, rfl⟩
    rcases hre with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)

def cmL (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) : PeriodPair :=
  scalePair (cmPair a b d ha hd) lam hlam

def CmOK (a : ℕ) (b c : ℤ) (d : ℕ) : Prop := 4 * (a : ℤ) * c = b ^ 2 + d ∧ Odd a ∧ d % 8 = 7 ∧ d.Prime

end PI.ULS

namespace PI

open PI.ULS in

def UnimodLocStd : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
      IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λa →
      (∀ x ∈ Λa, cmTheta b d • x ∈ Λa) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λa ≠ 0 →
      relIdx Λa (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∀ l : ℕ, l.Prime → ∃ δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
        IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
          (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧ (∀ x, δ x = x → x = 0) ∧
        relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 ∧
        ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ∧
        relIdx (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.UnimodularOrthogonalQ2
section
noncomputable section

namespace PI.UnimodularOrthogonalQ2

open NumberField

def OKpair (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) :
    Set (ℂ_[p] × ℂ_[p]) :=
  closure (Set.range fun a : 𝓞 K => (τ (a : K), τ (c (a : K))))

def hP {p : ℕ} [Fact p.Prime] {κ : Type} [Fintype κ] (x y : κ → ℂ_[p] × ℂ_[p]) : ℂ_[p] × ℂ_[p] :=
  ∑ k, x k * (y k).swap

def IsBasisOver {p : ℕ} [Fact p.Prime] (O : Set (ℂ_[p] × ℂ_[p])) {κ ι : Type} [Fintype ι]
    (Y : Set (κ → ℂ_[p] × ℂ_[p])) (b : ι → κ → ℂ_[p] × ℂ_[p]) : Prop :=
  (∀ e, b e ∈ Y) ∧ ∀ y ∈ Y, ∃! a : ι → ℂ_[p] × ℂ_[p], (∀ e, a e ∈ O) ∧ y = fun k => ∑ e, a e * b e k

def Stmt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) (d : ℕ) (b0 : K),
    Module.finrank ℚ K = 2 → (∃ x, c x ≠ x) → d.Prime → b0 ^ 2 = -(d : K) → p ≠ d → (p = 2 → d % 8 = 7) →
    ∀ (κ : Type) [Fintype κ] (r : ℕ) (Y : Set (κ → ℂ_[p] × ℂ_[p])) (b : Fin r → κ → ℂ_[p] × ℂ_[p]),
      IsBasisOver (OKpair K c p τ) Y b →
      (∀ a : Fin r → ℂ_[p] × ℂ_[p], (∀ e, a e ∈ OKpair K c p τ) → (fun k => ∑ e, a e * b e k) ∈ Y) →
      (∀ i j, hP (b i) (b j) ∈ OKpair K c p τ) →
      (∃ G : Fin r → Fin r → ℂ_[p] × ℂ_[p], (∀ i j, G i j ∈ OKpair K c p τ) ∧
        ∀ i k, ∑ j, hP (b i) (b j) * G j k = if i = k then 1 else 0) →
      ∃ b' : Fin r → κ → ℂ_[p] × ℂ_[p], IsBasisOver (OKpair K c p τ) Y b' ∧
        ∀ i j, hP (b' i) (b' j) = if i = j then 1 else 0

end PI.UnimodularOrthogonalQ2
end
end

-- bundled from Formalism.PeriodIntegrals.UnipVal
section
open NumberField IsDedekindDomain

noncomputable section

namespace PI.UnipVal

variable {K : Type} [Field K] [NumberField K]

def vw (w : HeightOneSpectrum (𝓞 K)) (a : K) : ℤ :=
  FractionalIdeal.count K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a)

def plc (w : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ w.asIdeal)

def ramw (w : HeightOneSpectrum (𝓞 K)) : ℤ := vw w ((plc w : ℕ) : K)

def UnipVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)),
    (∀ n : ℕ, n ≠ 0 → vw w ((n : ℕ) : K) = ramw w * (padicValNat (plc w) n : ℤ)) ∧
    ∀ g₁ g₂ a : ℕ, g₁.Prime → g₂.Prime → g₁ ≠ g₂ →
      (vw w (((g₁ ^ a * g₂ ^ a : ℕ)) : K) : ℝ) = (ramw w : ℝ) * (if plc w = g₁ ∨ plc w = g₂ then (a : ℝ) else 0)

end PI.UnipVal

end
end

-- bundled from Formalism.PeriodIntegrals.UnitDetRoot
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace PI

def UnitDetRootDefs.cmTheta (b : ℤ) (d : ℕ) : ℂ := ((b : ℂ) + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2

def UnitDetRootDefs.cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) : PeriodPair where
  ω₁ := (a : ℂ)
  ω₂ := UnitDetRootDefs.cmTheta b d
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [UnitDetRootDefs.cmTheta] at him hre
    have ht : t = 0 := by
      rcases him with h1 | h1
      · exact h1
      · exact absurd h1 (by positivity)
    subst ht
    simp at hre
    refine ⟨?_, rfl⟩
    rcases hre with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)

def UnitDetRootDefs.scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have h := L.indep
    rw [LinearIndependent.pair_iff] at h ⊢
    intro s t hst
    apply h s t
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.mp this).resolve_left hc

def UnitDetRootDefs.area (L : PeriodPair) : ℝ := |(conj L.ω₁ * L.ω₂).im|

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

abbrev UnitDetRootDefs.Sesq (V : Type*) [AddCommGroup V] [Module ℂ V] := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ

def UnitDetRootDefs.altE (H : UnitDetRootDefs.Sesq V) (x y : V) : ℝ := (H x y).im

def UnitDetRootDefs.dualLat (H : UnitDetRootDefs.Sesq V) (Λ : AddSubgroup V) : AddSubgroup V where
  carrier := {x | ∀ y ∈ Λ, ∃ m : ℤ, UnitDetRootDefs.altE H x y = (m : ℝ)}
  zero_mem' := fun y _ => ⟨0, by simp [UnitDetRootDefs.altE]⟩
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨m, hm⟩ := ha y hy
    obtain ⟨k, hk⟩ := hb y hy
    exact ⟨m + k, by simp only [UnitDetRootDefs.altE] at hm hk ⊢; simp [hm, hk]⟩
  neg_mem' := by
    intro a ha y hy
    obtain ⟨m, hm⟩ := ha y hy
    exact ⟨-m, by simp only [UnitDetRootDefs.altE] at hm ⊢; simp [hm]⟩

def UnitDetRootDefs.IsSelfDual (H : UnitDetRootDefs.Sesq V) (Λ : AddSubgroup V) : Prop := UnitDetRootDefs.dualLat H Λ = Λ

def UnitDetRootDefs.relIdx (Λ₁ Λ₂ : AddSubgroup V) : ℕ := Λ₁.relIndex Λ₂

def UnitDetRootDefs.IsIsom {W : Type*} [AddCommGroup W] [Module ℂ W] (H : UnitDetRootDefs.Sesq V) (H' : UnitDetRootDefs.Sesq W) (g : V →ₗ[ℂ] W) : Prop :=
  ∀ x y, H' (g x) (g y) = H x y

def UnitDetRootDefs.imgLat {W : Type*} [AddCommGroup W] [Module ℂ W] (g : V →ₗ[ℂ] W) (Λ : AddSubgroup V) : AddSubgroup W :=
  Λ.map g.toAddMonoidHom

end General

section Coordinates

variable {n : Type*} [Fintype n]

def UnitDetRootDefs.matH (h : Matrix n n ℂ) : UnitDetRootDefs.Sesq (n → ℂ) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => ∑ i, ∑ j, z i * h i j * conj (w j))
    (by intro a b c; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (by intro c a b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc])
    (by intro a b c; simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)

def UnitDetRootDefs.stdH (L : PeriodPair) (n : Type*) [Fintype n] [DecidableEq n] : UnitDetRootDefs.Sesq (n → ℂ) :=
  UnitDetRootDefs.matH (((UnitDetRootDefs.area L : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ))

def UnitDetRootDefs.stdLat (L : PeriodPair) (n : Type*) : AddSubgroup (n → ℂ) :=
  AddSubgroup.pi Set.univ fun _ => L.lattice.toAddSubgroup

end Coordinates

def UnitDetRootDefs.cmL (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) : PeriodPair :=
  UnitDetRootDefs.scalePair (UnitDetRootDefs.cmPair a b d ha hd) lam hlam

def UnitDetRootDefs.CmOK (a : ℕ) (b c : ℤ) (d : ℕ) : Prop := 4 * (a : ℤ) * c = b ^ 2 + d ∧ Odd a ∧ d % 8 = 7 ∧ d.Prime

def UnitDetRoot : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), UnitDetRootDefs.CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
      UnitDetRootDefs.IsSelfDual (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) Λa →
      (∀ x ∈ Λa, UnitDetRootDefs.cmTheta b d • x ∈ Λa) →
      UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) Λa ≠ 0 →
      UnitDetRootDefs.relIdx Λa (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ : ℂ ≃+* ℂ, ‖σ κ‖ = 1) ∧
        ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)),
          UnitDetRootDefs.IsIsom (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m)
            (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) →
          UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 →
          ¬ l ∣ UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) →
          UnitDetRootDefs.relIdx (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ 0 →
          ‖ι κ‖ ^ 2 * ‖ι (LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)))‖ = 1

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryApprox
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI

section Group

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def UnitaryApproxDefs.cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

def UnitaryApproxDefs.IsHerm (σ : A →+* A) (J : Matrix n n A) : Prop := UnitaryApproxDefs.cT σ J = J

theorem UnitaryApproxDefs.cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    UnitaryApproxDefs.cT σ (M * N) = UnitaryApproxDefs.cT σ N * UnitaryApproxDefs.cT σ M := by
  simp [UnitaryApproxDefs.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem UnitaryApproxDefs.cT_one (σ : A →+* A) : UnitaryApproxDefs.cT σ (1 : Matrix n n A) = 1 := by
  unfold UnitaryApproxDefs.cT
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

def UnitaryApproxDefs.UJ (σ : A →+* A) (J : Matrix n n A) : Subgroup (GL n A) where
  carrier := {g | UnitaryApproxDefs.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J}
  one_mem' := by simp [UnitaryApproxDefs.cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc UnitaryApproxDefs.cT σ ((a : Matrix n n A) * (b : Matrix n n A)) * J * ((a : Matrix n n A) * (b : Matrix n n A))
        = UnitaryApproxDefs.cT σ (b : Matrix n n A) * (UnitaryApproxDefs.cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
          rw [UnitaryApproxDefs.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc UnitaryApproxDefs.cT σ ((g⁻¹ : GL n A) : Matrix n n A) * J * ((g⁻¹ : GL n A) : Matrix n n A)
        = UnitaryApproxDefs.cT σ ((g⁻¹ : GL n A) : Matrix n n A) * (UnitaryApproxDefs.cT σ (g : Matrix n n A) * J * (g : Matrix n n A))
            * ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg]
      _ = UnitaryApproxDefs.cT σ ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) * J
            * ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by
          rw [UnitaryApproxDefs.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, UnitaryApproxDefs.cT_one, Matrix.one_mul, Matrix.mul_one]
end Group

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def UnitaryApproxDefs.sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom

def UnitaryApproxDefs.inclE (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom

def UnitaryApproxDefs.UPts (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type) [CommRing R] [Algebra F R] :
    Subgroup (GL n (E ⊗[F] R)) := UnitaryApproxDefs.UJ (UnitaryApproxDefs.sigR σ R) (J.map (UnitaryApproxDefs.inclE (F := F) R))

def UnitaryApproxDefs.tensInt (R : Type) [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R) :
    Subring (E ⊗[F] R) :=
  Subring.closure (Set.range (fun x : S₁ => (x : E) ⊗ₜ[F] (1 : R)) ∪
    Set.range (fun y : S₂ => (1 : E) ⊗ₜ[F] (y : R)))

def UnitaryApproxDefs.intOE (E : Type) [Field E] [NumberField E] : Subring E := (algebraMap (𝓞 E) E).range

end Points

def UnitaryApprox : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ e, σ (σ e) = e) → (∃ θ, σ θ ≠ θ) → UnitaryApproxDefs.IsHerm (σ : E →+* E) J → IsUnit J.det →
    ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ g ∈ UnitaryApproxDefs.UPts σ J (v.adicCompletion F), ∀ D : 𝓞 F, D ≠ 0 →
    ∃ γ ∈ UnitaryApproxDefs.UJ (σ : E →+* E) J, ∀ i j,
      ∃ s ∈ UnitaryApproxDefs.tensInt (F := F) (v.adicCompletion F) (UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers F).toSubring,
        (g : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
            UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) ((γ : Matrix n n E) i j) =
          UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (D : F)) * s

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryDense
section
open Matrix
open scoped ComplexOrder

namespace PI

def UnitaryDense : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ),
    (∀ u : Matrix (Fin n) (Fin n) ℂ, uᴴ * u = 1 →
      MvPolynomial.eval (fun x : Fin n × Fin n => u x.1 x.2) P = 0) → P = 0

def FramesDense : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (G : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, (G τ).PosDef) →
    ∀ P : MvPolynomial (ι × Fin n × Fin n) ℂ,
      (∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ)ᴴ * G τ * y τ = 1) →
        MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P = 0) → P = 0

def FramesDenseDet : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (G : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, (G τ).PosDef) →
    ∀ (s t : ι → ℤ) (P Q : MvPolynomial (ι × Fin n × Fin n) ℂ),
      (∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ)ᴴ * G τ * y τ = 1) →
        (∏ τ, (y τ).det ^ s τ) * MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P =
        (∏ τ, (y τ).det ^ t τ) * MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) Q) →
      ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ).det ≠ 0) →
        (∏ τ, (y τ).det ^ s τ) * MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P =
        (∏ τ, (y τ).det ^ t τ) * MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) Q

end PI
end

-- bundled from Formalism.PeriodIntegrals.VacEntire
section
noncomputable section

namespace PI.VacEntire

variable {ι : Type} [Fintype ι] {N N' : ℕ}

def Hf (A : ℝ) (z w : ι → Fin N' → Fin N → ℂ) : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (A : ℂ)

def al (d : ℕ) (A : ℝ) (x : ι → Fin N' → Fin N → ℂ) : ℂ :=
  (-1 : ℂ) ^ (round (Real.sqrt d / 2 * (Hf A x x).re))

def U (A : ℝ) (x : ι → Fin N' → Fin N → ℂ) (G : (ι → Fin N' → Fin N → ℂ) → ℂ) : (ι → Fin N' → Fin N → ℂ) → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * Hf A z x - (Real.pi : ℂ) * Hf A x x / 2)

def Iop (d : ℕ) (A : ℝ) (La₁ La₂ : AddSubgroup (ι → Fin N' → Fin N → ℂ))
    (G : (ι → Fin N' → Fin N → ℂ) → ℂ) : (ι → Fin N' → Fin N → ℂ) → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      al d A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) * U A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) G z

def tensPow {n : Type} [Fintype n] (θ : (n → ℂ) → ℂ) (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) : ℂ :=
  ∏ i : Fin N', ∏ j : Fin N, θ fun τ => z τ i j

def IopEntire : Prop :=
  ∀ (ι : Type) [Fintype ι] (N N' d : ℕ) (A : ℝ) (La₁ La₂ : AddSubgroup (ι → Fin N' → Fin N → ℂ))
    (G : (ι → Fin N' → Fin N → ℂ) → ℂ), AnalyticOnNhd ℂ G Set.univ → AnalyticOnNhd ℂ (Iop d A La₁ La₂ G) Set.univ

def TensEntire : Prop :=
  ∀ (n : Type) [Fintype n] (θ : (n → ℂ) → ℂ) (N N' : ℕ), AnalyticOnNhd ℂ θ Set.univ →
    AnalyticOnNhd ℂ (tensPow θ N N') Set.univ

def Target : Prop := IopEntire ∧ TensEntire

end PI.VacEntire
end
end

-- bundled from Formalism.PeriodIntegrals.WeakApproxDVR
section
noncomputable section

namespace PI

def WeakApproxDVR : Prop :=
  ∀ (E : Type) [Field E] (ι : Type) [Fintype ι] (W Q : ι → Type) [∀ i, CommRing (W i)]
    [∀ i, IsDomain (W i)] [∀ i, IsDiscreteValuationRing (W i)] [∀ i, Field (Q i)]
    [∀ i, Algebra (W i) (Q i)] [∀ i, IsFractionRing (W i) (Q i)] (iw : ∀ i, E →+* Q i) (p : ℕ),
    (∀ i, (p : Q i) ≠ 0) → (∀ i, ¬ IsUnit (p : W i)) →
    (∀ i (x : Q i) (N : ℕ), ∃ a : E, ∃ c : W i, iw i a = x + (p : Q i) ^ N * algebraMap (W i) (Q i) c) →
    (∀ i j, i ≠ j → ∃ a : E, iw i a ∈ Set.range (algebraMap (W i) (Q i)) ∧
      iw j a ∉ Set.range (algebraMap (W j) (Q j))) →
    ∀ (x : ∀ i, Q i) (N : ℕ), ∃ a : E, ∀ i, ∃ c : W i,
      iw i a = x i + (p : Q i) ^ N * algebraMap (W i) (Q i) c

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.WeylProd
section
namespace PI

open Finset

def vandN (x : ℕ → ℝ) (N : ℕ) : ℝ := ∏ i ∈ range N, ∏ j ∈ Ico (i + 1) N, (x i - x j)

noncomputable def dimVN (x : ℕ → ℝ) (N : ℕ) : ℝ := vandN x N / ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ)

def shiftSeq {n : ℕ} (w : Fin n → ℤ) : ℕ → ℝ := fun i => if h : i < n then ((w ⟨i, h⟩ : ℤ) : ℝ) - i else 0

def WeylProd : Prop :=
  ∀ (n : ℕ) (μ w : Fin n → ℤ) (c : ℤ), (∀ t, μ t = w t - c) →
    (((∏ i : Fin n, ∏ j : Fin n,
      if i < j then (((μ i : ℤ) : ℚ) - ((μ j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1 : ℚ)) : ℝ) = dimVN (shiftSeq w) n

end PI
end

