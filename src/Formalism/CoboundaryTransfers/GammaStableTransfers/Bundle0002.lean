import Formalism.CoboundaryTransfers.Bundle0001
import Formalism.WachModuleLifts.WachModuleProofs.WachModuleStatementHolds
import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.Bundle0001
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.Bundle0001
import Formalism.CoboundaryTransfers.StatementAPI
import Formalism.CoboundaryTransfers.GammaStableTransfers.Bundle0001
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound

-- bundled from Formalism.CoboundaryTransfers.GammaStableTransfers.BridgeCL
section
noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

theorem baseOfCL_qLin {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]
    (B : CL.W.Base p A) : (baseOfCL B).QLin := by
  show B.q = B.π₀ + ((p : ℕ) : A)
  rw [B.hq, map_natCast]

theorem wach_lattice_nonempty_Q : NonemptyQ := by
  intro p _
  obtain ⟨W, hN, hX⟩ := CL.W.wach_module_nonempty p
  refine ⟨baseOfCL (CL.W.polyBase p), ofCL W, rfl, hN, hX, ?_, baseOfCL_qLin _,
    (CL.W.polyBase p).hφ⟩
  show ¬ IsUnit (Polynomial.X + Polynomial.C (p : ℤ_[p]))
  exact Polynomial.not_isUnit_X_add_C _

end Formalism.CoboundaryTransfers
end
end

-- bundled from Formalism.CoboundaryTransfers.GammaStableTransfers.BridgeLIFT
section
noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

theorem pow_smul_bijective {A D : Type} [CommRing A] [AddCommGroup D] [Module A D] (Q : A)
    (h : Function.Bijective (fun x : D => Q • x)) (M : ℕ) :
    Function.Bijective (fun x : D => Q ^ M • x) := by
  have e : (fun x : D => Q ^ M • x) = (fun x : D => Q • x)^[M] := by
    funext x
    induction M with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ← ih, pow_succ', mul_smul]
  rw [e]
  exact h.iterate M

theorem lift_gamma_invariant_lattice : LIFTGammaQN := by
  intro ℓ _ A _ _ B M D _ _ _ _ W y hy
  obtain ⟨t, hv, hγQ⟩ := B.γQ
  obtain ⟨n, hn, hγn⟩ := W.γ_N _ hy
  obtain ⟨w, hw⟩ := hv.exists_left_inv
  have hX : B.X ∣ w - 1 := ⟨-(w * t), by linear_combination hw⟩
  obtain ⟨r, hr⟩ : B.X ∣ w ^ M - 1 := by
    have h := sub_dvd_pow_sub_pow w 1 M
    rw [one_pow] at h
    exact dvd_trans hX h
  have hw' : w ^ M = B.X * r + 1 := by rw [← hr]; ring
  have h1 : W.γ (B.Q ^ M • y) = B.Q ^ M • ((1 + B.X * t) ^ M • W.γ y) := by
    rw [W.γ_smul, map_pow, hγQ, mul_pow, mul_smul]
  have h2 : w ^ M • W.γ (B.Q ^ M • y) = B.Q ^ M • W.γ y := by
    rw [h1, smul_comm (w ^ M) (B.Q ^ M), ← mul_smul (w ^ M), ← mul_pow, hw, one_pow, one_smul]
  have h3 : W.γ (B.Q ^ M • y) = B.Q ^ M • y + B.X • n := by rw [← hγn]; abel
  have key : B.Q ^ M • (W.γ y - y) = B.X • (r • B.Q ^ M • y + w ^ M • n) := by
    rw [smul_sub, ← h2, h3, hw']
    module
  have hb := pow_smul_bijective B.Q W.Q_bij M
  obtain ⟨y', hy'⟩ := hb.2 (r • B.Q ^ M • y + w ^ M • n)
  simp only at hy'
  refine ⟨y', ?_, ?_⟩
  · rw [hy']
    exact W.N.add_mem (W.N.smul_mem _ hy) (W.N.smul_mem _ hn)
  · apply hb.1
    simp only
    rw [key, smul_comm (B.Q ^ M) B.X y', hy']

def sesOfLIFT {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
    {B : LIFT.Base ℓ A} {M : ℕ} {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    {W₀ : LIFT.WD B M D₀} {W₁ : LIFT.WD B M D₁} {W₂ : LIFT.WD B M D₂}
    (S : LIFT.SES W₀ W₁ W₂) :
    SES (ofLIFT W₀ (lift_gamma_invariant_lattice ℓ A B M D₀ W₀)) (ofLIFT W₁ (lift_gamma_invariant_lattice ℓ A B M D₁ W₁))
      (ofLIFT W₂ (lift_gamma_invariant_lattice ℓ A B M D₂ W₂)) where
  ι := ⟨S.ι.f, S.ι.φ_comm, S.ι.γ_comm, S.ι.N_le⟩
  π := ⟨S.π.f, S.π.φ_comm, S.π.γ_comm, S.π.N_le⟩
  ι_inj := S.ι_inj
  exact := S.exact
  sat := S.sat

theorem wach_lattice_nonempty_unramified : NonemptyU := by
  intro p _ u
  obtain ⟨B, W, hu, hN, hX⟩ := LIFT.wDNonempty_proof p u
  subst hu
  refine ⟨baseOfLIFT B, ofLIFT W (lift_gamma_invariant_lattice p _ B 0 _ W), rfl, hN, hX, B.γX, ?_⟩
  obtain ⟨t, ht, h⟩ := B.γQ
  refine ⟨1 + B.X * t, ht, ⟨t, rfl⟩, ?_⟩
  show B.γA B.Q = (1 + B.X * t) * B.Q
  rw [h, mul_comm]

end Formalism.CoboundaryTransfers
end
end

-- bundled from Formalism.CoboundaryTransfers.GammaStableTransfers.DepthPageFirstZetaFactorEqPrimePower
section
noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

namespace GammaInvariantLatticeLift

theorem gamma_invariant_lattice_lift {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D]
    [Module A D] [Module O D] [IsScalarTower O A D]
    (X Q v t : A) (γA : A →ₐ[O] A) (M : ℕ) (N : Submodule A D) (γ : D →ₗ[O] D)
    (hv : IsUnit v) (hvt : v = 1 + X * t) (hQ : γA Q = v * Q)
    (hbij : Function.Bijective (fun x : D => Q • x))
    (hsmul : ∀ (a : A) (x : D), γ (a • x) = γA a • γ x)
    (hN : ∀ x ∈ N, ∃ x' ∈ N, γ x - x = X • x') :
    ∀ y : D, Q ^ M • y ∈ N → ∃ y' : D, Q ^ M • y' ∈ N ∧ γ y - y = X • y' := by
  intro y hy
  have hit : ∀ k (x : D), (fun x : D => Q • x)^[k] x = Q ^ k • x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih => intro x; rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]
  have hbM : Function.Bijective (fun x : D => Q ^ M • x) := by
    have := hbij.iterate M
    convert this using 1
    funext x
    rw [hit]
  set w : A := ↑hv.unit⁻¹ with hw_def
  have hwv : w * v = 1 := hv.val_inv_mul
  have hw1 : w - 1 = X * (-(w * t)) := by
    have : w - 1 = w * (1 - v) := by rw [mul_sub, hwv, mul_one]
    rw [this, hvt]; ring
  obtain ⟨s, hs⟩ : X ∣ w ^ M - 1 := by
    have h1 := sub_dvd_pow_sub_pow w 1 M
    rw [one_pow] at h1
    exact (Dvd.intro _ hw1.symm).trans h1
  have hwM : w ^ M = 1 + X * s := by rw [← hs]; ring
  obtain ⟨n', hn'N, hn'⟩ := hN _ hy
  have e1 : (v * Q) ^ M • γ y = Q ^ M • y + X • n' := by
    rw [← hQ, ← map_pow, ← hsmul, ← hn']
    abel
  have key : Q ^ M • γ y = w ^ M • (Q ^ M • y + X • n') := by
    rw [← e1, smul_smul, mul_pow, ← mul_assoc, ← mul_pow, hwv, one_pow, one_mul]
  set m : D := s • (Q ^ M • y) + w ^ M • n' with hm_def
  have hmN : m ∈ N := N.add_mem (N.smul_mem _ hy) (N.smul_mem _ hn'N)
  have hQm : Q ^ M • (γ y - y) = X • m := by
    rw [smul_sub, key, hm_def, hwM]
    module
  obtain ⟨y', hy'⟩ := hbM.2 m
  refine ⟨y', ?_, ?_⟩
  · show Q ^ M • y' ∈ N
    have : Q ^ M • y' = m := hy'
    rw [this]; exact hmN
  · apply hbM.1
    show Q ^ M • (γ y - y) = Q ^ M • (X • y')
    have : Q ^ M • y' = m := hy'
    rw [hQm, smul_comm, this]

section Base

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

end Base

section Inst

variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : WachCohomologyFacts.Base O A} {E : WachCohomologyFacts.Amb B AA} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V]
  [Module O V] [IsScalarTower O AA V] [IsScalarTower O A V]

theorem smul_eq_alg (a : A) (v : V) : a • v = algebraMap A AA a • v :=
  (algebraMap_smul AA a v).symm

theorem smul_bij (_E : WachCohomologyFacts.Amb B AA) (a : A) (ha : IsUnit (algebraMap A AA a)) :
    Function.Bijective (fun x : ZMod n → V => a • x) := by
  obtain ⟨u, hu⟩ := ha
  refine Function.bijective_iff_has_inverse.mpr ⟨fun x j => (↑u⁻¹ : AA) • x j, ?_, ?_⟩
  · intro x
    funext j
    show (↑u⁻¹ : AA) • (a • x j) = x j
    rw [smul_eq_alg (AA := AA) a (x j), ← hu, smul_smul, Units.inv_mul, one_smul]
  · intro x
    funext j
    show a • ((↑u⁻¹ : AA) • x j) = x j
    rw [smul_eq_alg (AA := AA) a, ← hu, smul_smul, Units.mul_inv, one_smul]

theorem Φ_smul (W : WachCohomologyFacts.WachDatum E n V) (a : A) (x : ZMod n → V) :
    W.Φ (a • x) = B.φ a • W.Φ x := by
  funext j
  show W.φ (j - 1) (a • x (j - 1)) = B.φ a • W.φ (j - 1) (x (j - 1))
  rw [smul_eq_alg (AA := AA) a, W.φ_smul, E.φ_ext, ← smul_eq_alg]

theorem Γ_smul (W : WachCohomologyFacts.WachDatum E n V) (a : A) (x : ZMod n → V) :
    W.Γ (a • x) = B.γ a • W.Γ x := by
  funext j
  show W.γ j (a • x j) = B.γ a • W.γ j (x j)
  rw [smul_eq_alg (AA := AA) a, W.γ_smul, E.γ_ext, ← smul_eq_alg]

theorem Γ_sub (W : WachCohomologyFacts.WachDatum E n V) :
    ∀ x ∈ Submodule.pi Set.univ W.N, ∃ x' ∈ Submodule.pi Set.univ W.N, W.Γ x - x = B.X • x' := by
  intro x hx
  rw [Submodule.mem_pi] at hx
  choose x' hx' he using fun j => W.γ_sub j (x j) (hx j (Set.mem_univ j))
  exact ⟨x', (Submodule.mem_pi).2 fun j _ => hx' j, funext fun j => he j⟩

theorem γq (B : WachCohomologyFacts.Base O A) : B.γ B.q = (1 + B.X * B.c) * B.q := by
  show B.γ (B.X + (B.ℓ : A)) = (1 + B.X * B.c) * (B.X + (B.ℓ : A))
  rw [map_add, map_natCast]
  linear_combination B.hγX

def toWach (W : WachCohomologyFacts.WachDatum E n V) (M : ℕ) (hc : IsUnit (1 + B.X * B.c))
    (hM : ∀ i, ∀ x ∈ W.N i, B.q ^ M • W.φ i x ∈ W.N (i + 1)) :
    WachMod (baseOfArchimedeanComponents B) M (ZMod n → V) where
  N := Submodule.pi Set.univ W.N
  φ := W.Φ
  γ := W.Γ
  φ_smul := Φ_smul W
  γ_smul := Γ_smul W
  comm := fun x => (WachCohomologyFacts.PCoh.ΓΦ_comm W x).symm
  X_inj := by
    intro x hx
    exact (smul_bij E B.X E.hX).1 (hx.trans (smul_zero _).symm)
  Q_bij := smul_bij E B.q E.hq
  φ_N := by
    intro x hx
    rw [Submodule.mem_pi] at hx ⊢
    intro j _
    have := hM (j - 1) (x (j - 1)) (hx (j - 1) (Set.mem_univ _))
    rw [sub_add_cancel] at this
    exact this
  γ_N := Γ_sub W
  γ_QN := gamma_invariant_lattice_lift B.X B.q (1 + B.X * B.c) B.c B.γ M (Submodule.pi Set.univ W.N) W.Γ hc rfl
    (γq B) (smul_bij E B.q E.hq) (Γ_smul W) (Γ_sub W)

end Inst

section Agree

variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : WachCohomologyFacts.Base O A} {E : WachCohomologyFacts.Amb B AA} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V]
  [Module O V] [IsScalarTower O AA V] [IsScalarTower O A V] {M : ℕ}
  (W' : WachMod (baseOfArchimedeanComponents B) M (ZMod n → V)) (W : WachCohomologyFacts.WachDatum E n V)

end Agree

section HomPart

variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : WachCohomologyFacts.Base O A} {E : WachCohomologyFacts.Amb B AA} {n : ℕ}
  {V₁ : Type} [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
  [Module O V₁] [IsScalarTower O AA V₁] [IsScalarTower O A V₁]
  {V₂ : Type} [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
  [Module O V₂] [IsScalarTower O AA V₂] [IsScalarTower O A V₂]
  {W₁ : WachCohomologyFacts.WachDatum E n V₁} {W₂ : WachCohomologyFacts.WachDatum E n V₂}

def fA (hm : WachCohomologyFacts.Hom W₁ W₂) : (ZMod n → V₁) →ₗ[A] (ZMod n → V₂) :=
  LinearMap.pi (fun j => (hm.f.restrictScalars A).comp (LinearMap.proj j))

theorem fA_apply (hm : WachCohomologyFacts.Hom W₁ W₂) (x : ZMod n → V₁) : fA hm x = hm.fD x := rfl

def toHom (hm : WachCohomologyFacts.Hom W₁ W₂) {M : ℕ}
    (W₁' : WachMod (baseOfArchimedeanComponents B) M (ZMod n → V₁)) (W₂' : WachMod (baseOfArchimedeanComponents B) M (ZMod n → V₂))
    (hN₁ : W₁'.N = Submodule.pi Set.univ W₁.N) (hφ₁ : ⇑W₁'.φ = ⇑W₁.Φ) (hγ₁ : ⇑W₁'.γ = ⇑W₁.Γ)
    (hN₂ : W₂'.N = Submodule.pi Set.univ W₂.N) (hφ₂ : ⇑W₂'.φ = ⇑W₂.Φ) (hγ₂ : ⇑W₂'.γ = ⇑W₂.Γ) :
    Hom W₁' W₂' where
  f := fA hm
  φ_comm := by
    intro x
    rw [congrFun hφ₁ x, congrFun hφ₂, fA_apply, fA_apply]
    exact WachCohomologyFacts.PCoh.fD_Φ hm x
  γ_comm := by
    intro x
    rw [congrFun hγ₁ x, congrFun hγ₂, fA_apply, fA_apply]
    exact WachCohomologyFacts.PCoh.fD_Γ hm x
  N_le := by
    intro x hx
    rw [hN₁, Submodule.mem_pi] at hx
    rw [hN₂, Submodule.mem_pi]
    intro j _
    exact hm.N_le j (x j) (hx j (Set.mem_univ j))

end HomPart

end GammaInvariantLatticeLift

end Formalism.CoboundaryTransfers
end
end

-- bundled from Formalism.CoboundaryTransfers.GammaStableTransfers.GammaStableOfGammaQUnitHolds
section
noncomputable section

namespace Formalism.CoboundaryTransfers

section SlopeTestRemainingChoices

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]

private theorem WachMod.mem_cocycles_units_iff (W : WachMod B M D) (pr : D × D) :
    pr ∈ W.Z1 ↔ W.d1 pr.1 pr.2 = 0 := by
  simp [WachMod.Z1, WachMod.d1, sub_eq_add_neg]

private theorem WachMod.WachMod_mem_B1_iff (W : WachMod B M D) (pr : D × D) :
    pr ∈ W.B1 ↔ ∃ x, (W.φ x - x, W.γ x - x) = pr := by
  simp [WachMod.B1]

end SlopeTestRemainingChoices

theorem homPreservesCochains_holds : HomMaps := by
  intro O A _ _ _ B M D D' _ _ _ _ _ _ _ _ W W' F
  have hQ : ∀ y, W.QInv y → W'.QInv (F.f y) := fun y hy => by
    show B.Q ^ M • F.f y ∈ W'.N
    rw [← map_smul]
    exact F.N_le _ hy
  have hX : ∀ z, W.XN z → W'.XN (F.f z) := by
    rintro z ⟨n, hn, rfl⟩
    exact ⟨F.f n, F.N_le n hn, map_smul _ _ _⟩
  have hC1 : ∀ y z, W.C1 y z → W'.C1 (F.f y) (F.f z) := fun y z h => ⟨hQ y h.1, hX z h.2⟩
  have hd : ∀ y z, F.f (W.d1 y z) = W'.d1 (F.f y) (F.f z) := fun y z => by
    simp only [WachMod.d1, map_sub, F.φ_comm, F.γ_comm]
  have hZ1 : W.Z1.map F.f2 ≤ W'.Z1 := by
    rintro _ ⟨pr, hpr, rfl⟩
    refine (WachMod.mem_cocycles_units_iff W' _).mpr ?_
    show W'.d1 (F.f pr.1) (F.f pr.2) = 0
    rw [← hd, (WachMod.mem_cocycles_units_iff W pr).mp hpr, map_zero]
  have hB1 : W.B1.map F.f2 ≤ W'.B1 := by
    rintro _ ⟨pr, hpr, rfl⟩
    obtain ⟨x, rfl⟩ := (WachMod.WachMod_mem_B1_iff W pr).mp hpr
    exact (WachMod.WachMod_mem_B1_iff W' _).mpr ⟨F.f x, by simp [Hom.f2, F.φ_comm, F.γ_comm]⟩
  have hZf : W.Zf.map F.f2 ≤ W'.Zf := by
    refine Submodule.map_le_iff_le_comap.mpr ?_
    rw [WachMod.Zf]
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro pr ⟨hz, a, b, hb, hint⟩
      refine Submodule.mem_comap.mpr ?_
      rw [WachMod.Zf]
      apply Submodule.mem_sup_left
      apply Submodule.subset_span
      refine ⟨hZ1 ⟨pr, hz, rfl⟩, a, F.f2 b, hB1 ⟨b, hb, rfl⟩, ?_⟩
      obtain ⟨⟨k, hk⟩, hxn⟩ := hint
      have e : (B.p ^ a : ℕ) • F.f2 pr + F.f2 b = F.f2 ((B.p ^ a : ℕ) • pr + b) := by
        rw [map_add, map_nsmul]
      rw [e]
      refine ⟨⟨k, ?_⟩, hX _ hxn⟩
      show B.Q ^ k • F.f (((B.p ^ a : ℕ) • pr + b).1) ∈ W'.N
      rw [← map_smul]
      exact F.N_le _ hk
    · intro pr hpr
      refine Submodule.mem_comap.mpr ?_
      rw [WachMod.Zf]
      exact Submodule.mem_sup_right (hB1 ⟨pr, hpr, rfl⟩)
  refine ⟨hQ, hX, ?_, hd, ?_, ?_, ?_, hZ1, hB1, hZf⟩
  · rintro ω ⟨y, hy, rfl⟩
    exact ⟨F.f y, hQ y hy, map_smul _ _ _⟩
  · rintro y z ⟨h1, h2⟩
    exact ⟨hC1 y z h1, by rw [← hd, h2, map_zero]⟩
  · rintro y z ⟨x, hx, rfl, rfl⟩
    exact ⟨F.f x, F.N_le x hx, by rw [map_sub, F.φ_comm], by rw [map_sub, F.γ_comm]⟩
  · rintro ω ⟨y, z, h, rfl⟩
    exact ⟨F.f y, F.f z, hC1 y z h, hd y z⟩

theorem gammaStableOfGammaQUnit_holds : GammaQNOf := by
  intro O A _ _ _ B M D _ _ _ _ N γ hG hQ hγ hN y hy
  obtain ⟨v, hvu, ⟨t, hvt⟩, hγQ⟩ := hG
  have hit : ∀ (k : ℕ) (x : D), (fun x : D => B.Q • x)^[k] x = B.Q ^ k • x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih => intro x; rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]
  have hQM : Function.Bijective (fun x : D => B.Q ^ M • x) := by
    have h := hQ.iterate M
    rwa [show (fun x : D => B.Q • x)^[M] = fun x => B.Q ^ M • x from funext (hit M)] at h
  have hvk : ∀ k : ℕ, ∃ s : A, v ^ k = 1 + B.X * s := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨s, hs⟩ := ih
      exact ⟨s + t + B.X * s * t, by rw [pow_succ, hs, hvt]; ring⟩
  obtain ⟨s, hs⟩ := hvk M
  have hγn : γ (B.Q ^ M • y) = v ^ M • B.Q ^ M • γ y := by
    rw [hγ, map_pow, hγQ, mul_pow, mul_smul]
  obtain ⟨n', hn'N, hn'⟩ := hN _ hy
  obtain ⟨u, hu⟩ := hvu.pow M
  have hQγ : B.Q ^ M • γ y ∈ N := by
    have h1 : γ (B.Q ^ M • y) ∈ N := by
      have e : γ (B.Q ^ M • y) = B.Q ^ M • y + B.X • n' := by rw [← hn']; abel
      rw [e]
      exact N.add_mem hy (N.smul_mem _ hn'N)
    have h2 : B.Q ^ M • γ y = ((u⁻¹ : Aˣ) : A) • γ (B.Q ^ M • y) := by
      rw [hγn, ← hu, smul_smul, Units.inv_mul, one_smul]
    rw [h2]
    exact N.smul_mem _ h1
  have hmN : n' - s • B.Q ^ M • γ y ∈ N := N.sub_mem hn'N (N.smul_mem _ hQγ)
  have hkey : B.Q ^ M • (γ y - y) = B.X • (n' - s • B.Q ^ M • γ y) := by
    have e : (1 + B.X * s) • B.Q ^ M • γ y - B.Q ^ M • y = B.X • n' := by
      rw [← hs, ← hγn]
      exact hn'
    rw [smul_sub, smul_sub, ← e, add_smul, one_smul, mul_smul]
    abel
  obtain ⟨y', hy'⟩ := hQM.2 (n' - s • B.Q ^ M • γ y)
  simp only at hy'
  refine ⟨y', by rw [hy']; exact hmN, ?_⟩
  apply hQM.1
  show B.Q ^ M • (γ y - y) = B.Q ^ M • (B.X • y')
  rw [hkey, smul_comm (B.Q ^ M) B.X y', hy']

theorem cokernelLengthBound_holds : ColBound := by
  intro O A _ _ _ B M D D' _ _ _ _ _ _ _ _ W W' F g e hfin hlift
  obtain ⟨s, hs, hspan⟩ := hfin
  show Module.length O (↥W'.Zf ⧸ F.ImF.comap W'.Zf.subtype) ≤ _
  first
    | exact Formalism.WachCohomologyFacts.quotientLengthBound_holds O (D' × D') B.p g e W'.Zf W'.B1 F.ImF s hs hspan le_sup_right hlift
    | exact Formalism.WachCohomologyFacts.PLenBound.quotientLengthBound_holds O (D' × D') B.p g e W'.Zf W'.B1 F.ImF s hs hspan le_sup_right hlift
    | exact _root_.quotientLengthBound_holds O (D' × D') B.p g e W'.Zf W'.B1 F.ImF s hs hspan le_sup_right hlift

theorem finiteClassesLift_holds : LiftHf := by
  intro O A _ _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g eW c
    hnat hcl₁ hint hlifts κ hκ
  obtain ⟨pr, hcoc, hpr⟩ := hint.2 κ hκ
  obtain ⟨y₁, z₁, hcoc₁, hy, hz⟩ := hlifts _ _ hcoc
  have hmem : ((y₁, z₁) : D₁ × D₁) ∈ W₁.Z1 := (WachMod.mem_cocycles_units_iff W₁ _).mpr hcoc₁.2
  refine ⟨cl₁ ⟨(y₁, z₁), hmem⟩, hcl₁ _ hcoc₁, ?_⟩
  have hpr' : ((c • pr : W₂.Z1) : D₂ × D₂) = S.π.f2 (⟨(y₁, z₁), hmem⟩ : W₁.Z1) := by
    show c • (pr : D₂ × D₂) = (S.π.f y₁, S.π.f z₁)
    rw [hy, hz]
    rfl
  rw [hnat _ _ hpr', map_smul, hpr, smul_smul, mul_comm]

end Formalism.CoboundaryTransfers
end
end

