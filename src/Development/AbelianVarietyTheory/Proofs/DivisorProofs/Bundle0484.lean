import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0421
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0468

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantValuationOrderSum
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem iotaScalar_of_freeForm : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ) (Φ : FreeForm D N ψ) (τ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta τ f → ∀ ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → ∃ l₀ : C, v l₀ = v lam ∧ IotaScalar (Φ.F.map ((algebraMap O C).comp f)) (Φ.G.map ((algebraMap O C).comp f)) (D.lieRank τ) l₀ := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D ψ Φ τ f hf ι lam hι hlat
  obtain ⟨-, -, -, hθs, -, -, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := hθs y
    exact ⟨a ⊗ₜ 1, by rw [hf]; simp⟩
  obtain ⟨⟨-, hTtop, hTrk⟩, ⟨-, hHtop, hHrk⟩⟩ := GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ N h hh D
  obtain ⟨πT, hπT⟩ := GlobalTheory.T.exists_theta_projection p O C Λ N h τ f Φ.eT hf
  obtain ⟨πH, hπH⟩ := GlobalTheory.T.exists_theta_projection p O C Λ N h τ f Φ.eM hf
  obtain ⟨qT, hqT, hqTL⟩ : ∃ q : eig C (actT D) τ ≃ₗ[C] (Fin N → C), (∀ x, q x = πT x) ∧
      ∀ x, x ∈ quotLattice C (actT D) τ ↔ ∀ i, q x i ∈ (algebraMap O C).range :=
    GlobalTheory.T.theta_projection_surjective_eigen p O C Λ N h τ f (rhoTA D) Φ.eT πT hinj hθs hfs hf Φ.frameT hπT hTtop (hTrk τ)
  obtain ⟨qH, hqH, hqHL⟩ : ∃ q : eig C (actH D) τ ≃ₗ[C] (Fin N → C), (∀ x, q x = πH x) ∧
      ∀ x, x ∈ quotLattice C (actH D) τ ↔ ∀ i, q x i ∈ (algebraMap O C).range :=
    GlobalTheory.T.theta_projection_surjective_eigen p O C Λ N h τ f D.ρM Φ.eM πH hinj hθs hfs hf Φ.frameM hπH hHtop (hHrk τ)
  obtain ⟨δT, hδT, hδTL⟩ := GlobalTheory.T.exists_det_line_coordinate_iso C O Λ h N (actT D) τ qT hqTL
  obtain ⟨δH, hδH, hδHL⟩ := GlobalTheory.T.exists_det_line_coordinate_iso C O Λ h N (actH D) τ qH hqHL
  obtain ⟨l₀, hl₀v, hl₀⟩ := GlobalTheory.T.lattice_scaling_valuation_eq C v O _ _
    (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N))
    (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) δT δH ι lam hv
    (fun w => hδTL w) (fun w => hδHL w) hlat
  obtain ⟨-, -, hGρ, -, -⟩ := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
  have hG : ∀ l, D.G.map (WittVector.fontaineTheta O p) * actH D l =
      actT D l * D.G.map (WittVector.fontaineTheta O p) := by
    intro l
    have e := congrArg (fun M => M.map (WittVector.fontaineTheta O p)) (hGρ l)
    simpa [Matrix.map_mul, actH, actT, rhoTA, Matrix.map_map, padicToO] using e
  have hF : ∀ l, D.F.map (WittVector.fontaineTheta O p) * actT D l =
      actH D l * D.F.map (WittVector.fontaineTheta O p) := by
    intro l
    have e := congrArg (fun M => M.map (WittVector.fontaineTheta O p)) (D.F_act l)
    simpa [Matrix.map_mul, actH, actT, Matrix.map_map, padicToO] using e
  have hbmem : ∀ y : eig C (actH D) τ, bC C D y ∈ eig C (actT D) τ := by
    intro y
    apply (GlobalTheory.T.intertwiner_maps_eigenspaces C O Λ h (actH D) (actT D) _ hG).1 τ
    exact ⟨y, y.2, rfl⟩
  have hamem : ∀ x : eig C (actT D) τ, alC C D x ∈ eig C (actH D) τ := by
    intro x
    apply (GlobalTheory.T.intertwiner_maps_eigenspaces C O Λ h (actT D) (actH D) _ hF).1 τ
    exact ⟨x, x.2, rfl⟩
  refine ⟨l₀, hl₀v, ?_⟩
  intro X Y hX hY
  have h1 : ∀ i : Fin N, (i : ℕ) < D.lieRank τ →
      ((qT.symm (X i) : eig C (actT D) τ) : Fin h → C) = bC C D (qH.symm (Y i)) := by
    intro i hi
    have hz : qT ⟨bC C D (qH.symm (Y i)), hbmem _⟩ = X i := by
      rw [hqT]
      show πT (redC C D.G (qH.symm (Y i))) = X i
      rw [GlobalTheory.T.theta_projection_intertwining p O C Λ N h f Φ.eM Φ.eT πH πT D.G Φ.G hπH hπT Φ.matG, ← hqH,
        qH.apply_symm_apply, hX i hi]
    rw [← hz, qT.symm_apply_apply]
  have h2 : ∀ i : Fin N, D.lieRank τ ≤ (i : ℕ) →
      ((qH.symm (Y i) : eig C (actH D) τ) : Fin h → C) = alC C D (qT.symm (X i)) := by
    intro i hi
    have hz : qH ⟨alC C D (qT.symm (X i)), hamem _⟩ = Y i := by
      rw [hqH]
      show πH (redC C D.F (qT.symm (X i))) = Y i
      rw [GlobalTheory.T.theta_projection_intertwining p O C Λ N h f Φ.eT Φ.eM πT πH D.F Φ.F hπT hπH Φ.matF, ← hqT,
        qT.apply_symm_apply, hY i hi]
    rw [← hz, qH.symm_apply_apply]
  have e := hl₀ (exteriorPower.ιMulti C N fun i => qT.symm (X i))
  rw [hι _ _ h1 h2, hδH, hδT] at e
  simpa using e

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowersPrimeUnique
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.DivPowLPrime

theorem lPrime_eq_pow (l : ℕ) : lPrime l = l ^ lPrimeExp l := by
  unfold lPrime lPrimeExp; split_ifs with h <;> simp [h]

theorem one_le_lPrimeExp (l : ℕ) : 1 ≤ lPrimeExp l := by
  unfold lPrimeExp; split_ifs <;> norm_num

theorem isUnit_natCast_of_coprime {O : Type} [CommRing O] [IsLocalRing O] {l c : ℕ}
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hc : Nat.Coprime l c) : IsUnit (c : O) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  by_contra hu
  have hm : (c : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hu
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    have h := congrArg (Int.cast : ℤ → O) hab
    push_cast at h
    rw [← h]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hm)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

def factPrimePart (l m : ℕ) : ℕ := ordCompl[l] m.factorial

def qExp (l m : ℕ) : ℕ := lPrimeExp l * m - padicValNat l m.factorial

def qCoef (O : Type) [CommRing O] (l m : ℕ) : O :=
  (l : O) ^ qExp l m * Ring.inverse (factPrimePart l m : O)

theorem factorial_eq {l : ℕ} (hl : l.Prime) (m : ℕ) :
    m.factorial = l ^ padicValNat l m.factorial * factPrimePart l m := by
  rw [factPrimePart, ← Nat.factorization_def _ hl]
  exact (Nat.ordProj_mul_ordCompl_eq_self _ _).symm

section Lemmas

variable {O : Type} [CommRing O] [IsLocalRing O] {l : ℕ}

theorem isUnit_factPrimePart (hl : l.Prime) (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O) (m : ℕ) :
    IsUnit (factPrimePart l m : O) :=
  isUnit_natCast_of_coprime hlO (Nat.coprime_ordCompl hl (Nat.factorial_ne_zero m))

theorem factorial_mul_qCoef (hl : l.Prime) (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O) (m : ℕ)
    (hv : padicValNat l m.factorial ≤ lPrimeExp l * m) :
    (m.factorial : O) * qCoef O l m = (lPrime l : O) ^ m := by
  have hu := isUnit_factPrimePart hl hlO m
  have hf : (m.factorial : O) = (l : O) ^ padicValNat l m.factorial * (factPrimePart l m : O) := by
    have h := congrArg (Nat.cast : ℕ → O) (factorial_eq hl m)
    rwa [Nat.cast_mul, Nat.cast_pow] at h
  rw [hf, qCoef, qExp, lPrime_eq_pow, Nat.cast_pow, ← pow_mul]
  calc (l : O) ^ padicValNat l m.factorial * (factPrimePart l m : O) *
        ((l : O) ^ (lPrimeExp l * m - padicValNat l m.factorial) * Ring.inverse (factPrimePart l m : O))
      = (l : O) ^ (padicValNat l m.factorial + (lPrimeExp l * m - padicValNat l m.factorial)) *
          ((factPrimePart l m : O) * Ring.inverse (factPrimePart l m : O)) := by rw [pow_add]; ring
    _ = _ := by rw [Ring.mul_inverse_cancel _ hu, Nat.add_sub_cancel' hv, mul_one]

theorem qCoef_eq_mul {m : ℕ} (h : lPrimeExp l ≤ qExp l m) :
    qCoef O l m = (lPrime l : O) * ((l : O) ^ (qExp l m - lPrimeExp l) * Ring.inverse (factPrimePart l m : O)) := by
  rw [qCoef, lPrime_eq_pow, Nat.cast_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

end Lemmas

theorem dividedPowers_lPrime : ∀ (l : ℕ), l.Prime → (∀ m : ℕ, (1 ≤ m → lPrimeExp l + padicValNat l m.factorial ≤ lPrimeExp l * m) ∧ m + 2 * padicValNat l m.factorial ≤ 2 * (lPrimeExp l * m)) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R], (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) → ∀ γ₀ : DividedPowers (Ideal.span {(l : R)}), (∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)}, (m.factorial : R) * γ₀.dpow m y = y ^ m) → ∃ γ : DividedPowers (Ideal.span {(lPrime l : R)}), (∀ m : ℕ, ∃ q : O, (m.factorial : O) * q = (lPrime l : O) ^ m ∧ ∀ x : R, γ.dpow m ((lPrime l : R) * x) = algebraMap O R q * x ^ m) ∧ (∀ (m : ℕ), ∀ y ∈ Ideal.span {(lPrime l : R)}, γ.dpow m y = γ₀.dpow m y) ∧ ∀ n : ℕ, 1 ≤ n → γ.IsSubDPIdeal (Ideal.span {(lPrime l : R) ^ n}) ∧ ∀ (r : ℕ) (m : Fin r → ℕ) (x : Fin r → R), (∀ i, x i ∈ Ideal.span {(lPrime l : R)}) → 2 * n * lPrimeExp l ≤ ∑ i, m i → ∏ i, γ.dpow (m i) (x i) ∈ Ideal.span {(lPrime l : R) ^ n} := by
  intro l hl hnum O _ _ _ _ hlO R _ _ htf γ₀ hγ₀
  have hv : ∀ m : ℕ, padicValNat l m.factorial ≤ lPrimeExp l * m := fun m => by
    have := (hnum m).2; generalize lPrimeExp l * m = a at *; omega
  have hq : ∀ m : ℕ, (m.factorial : O) * qCoef O l m = (lPrime l : O) ^ m := fun m =>
    factorial_mul_qCoef hl hlO m (hv m)
  have hqe : ∀ m : ℕ, 1 ≤ m → lPrimeExp l ≤ qExp l m := fun m hm => by
    have := (hnum m).1 hm; unfold qExp; generalize lPrimeExp l * m = a at *; omega
  have hle : Ideal.span {(lPrime l : R)} ≤ Ideal.span {(l : R)} := by
    refine Ideal.span_singleton_le_span_singleton.2 ⟨(l : R) ^ (lPrimeExp l - 1), ?_⟩
    rw [lPrime_eq_pow, Nat.cast_pow, ← pow_succ', Nat.sub_add_cancel (one_le_lPrimeExp l)]
  have hform0 : ∀ (m : ℕ) (x : R), γ₀.dpow m ((lPrime l : R) * x) = algebraMap O R (qCoef O l m) * x ^ m := by
    intro m x
    have hmem : (lPrime l : R) * x ∈ Ideal.span {(l : R)} :=
      hle (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    apply sub_eq_zero.1
    apply htf m.factorial _ (Nat.factorial_ne_zero m)
    rw [mul_sub, hγ₀ m _ hmem, ← mul_assoc, ← map_natCast (algebraMap O R) m.factorial, ← map_mul, hq m, map_pow,
      map_natCast, mul_pow, sub_self]
  have hsub : γ₀.IsSubDPIdeal (Ideal.span {(lPrime l : R)}) :=
    { isSubideal := hle
      dpow_mem := fun n hn j hj => by
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hj
        rw [mul_comm, hform0, qCoef_eq_mul (hqe n (by omega)), map_mul, map_natCast, mul_assoc]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _) }
  let γ := DividedPowers.IsSubDPIdeal.dividedPowers γ₀ hsub
  have hγeq : ∀ (m : ℕ), ∀ y ∈ Ideal.span {(lPrime l : R)}, γ.dpow m y = γ₀.dpow m y := fun m y hy =>
    DividedPowers.IsSubDPIdeal.dpow_eq_of_mem γ₀ hsub hy
  have hform : ∀ (m : ℕ) (x : R), γ.dpow m ((lPrime l : R) * x) = algebraMap O R (qCoef O l m) * x ^ m := by
    intro m x
    rw [hγeq m _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)), hform0]
  refine ⟨γ, fun m => ⟨qCoef O l m, hq m, hform m⟩, hγeq, fun n hn => ⟨?_, ?_⟩⟩
  · exact
    { isSubideal := Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ (by omega))
      dpow_mem := fun m hm j hj => by
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hj
        have hy : y * (lPrime l : R) ^ n = (lPrime l : R) * (y * (lPrime l : R) ^ (n - 1)) := by
          rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel hn]
        rw [hy, hform, qCoef_eq_mul (hqe m (by omega)), map_mul, map_natCast, mul_pow]
        apply Ideal.mem_span_singleton.2
        have h1 : n - 1 ≤ (n - 1) * m := Nat.le_mul_of_pos_right _ (by omega)
        have hd : (lPrime l : R) ^ n ∣ (lPrime l : R) * ((lPrime l : R) ^ (n - 1)) ^ m := by
          rw [← pow_mul, ← pow_succ']
          exact pow_dvd_pow _ (by omega)
        exact hd.trans (Dvd.intro (algebraMap O R ((l : O) ^ (qExp l m - lPrimeExp l) *
          Ring.inverse (factPrimePart l m : O)) * y ^ m) (by ring)) }
  · intro r m x hx hsum
    choose y hy using fun i => Ideal.mem_span_singleton'.1 (hx i)
    have hp : ∏ i, γ.dpow (m i) (x i) = algebraMap O R (∏ i, qCoef O l (m i)) * ∏ i, y i ^ m i := by
      rw [map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← hy i, mul_comm, hform]
    have hprod : ∏ i, qCoef O l (m i) =
        (l : O) ^ (∑ i, qExp l (m i)) * ∏ i, Ring.inverse (factPrimePart l (m i) : O) := by
      simp only [qCoef, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have h2 : ∀ i, m i ≤ 2 * qExp l (m i) := fun i => by
      have := (hnum (m i)).2; unfold qExp; generalize lPrimeExp l * m i = a at *; omega
    have h3 : ∑ i, m i ≤ 2 * ∑ i, qExp l (m i) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => h2 i
    have hN : lPrimeExp l * n ≤ ∑ i, qExp l (m i) := by nlinarith
    rw [hp, Ideal.mem_span_singleton, hprod, map_mul, map_pow, map_natCast, lPrime_eq_pow, Nat.cast_pow, ← pow_mul]
    exact ((pow_dvd_pow _ hN).mul_right _).mul_right _

end GlobalTheory.DivPowLPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrDeterminantFrameRank
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] {C : Type} [Field C] [Algebra O C]

theorem incl_apply' (h : ℕ) (l : Fin h → O) : incl C h l = fun i => algebraMap O C (l i) := rfl

theorem incl_mem_eig {Λ : Type} [CommRing Λ] {h : ℕ} (ρ : Λ → Matrix (Fin h) (Fin h) O)
    (σ : Λ →+* O) (l : Fin h → O) (hl : ∀ a, ρ a *ᵥ l = σ a • l) : incl C h l ∈ eig C ρ σ := by
  simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  intro a
  funext i
  have e := congrFun (hl a) i
  simp only [incl_apply', Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [← map_mul, ← e, RingHom.map_mulVec]
  rfl

end SlopeTestRemainingChoices

section Parts

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {C : Type} [Field C] [Algebra O C]
  {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

theorem card_eq_lieRank (hinj : Function.Injective (algebraMap O C)) (D : Datum ε h Λ)
    (τ : Λ →+* O) {a : ℕ} (x : Fin a → Fin h → C) (hx : IsBasisOf C (lieSub C D τ) x) :
    a = D.lieRank τ := by
  haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
  have hincl : Function.Injective (incl C h : (Fin h → O) →ₗ[O] (Fin h → C)) := by
    intro u u' e
    funext i
    exact hinj (congrFun e i)
  have hliO : LinearIndependent O x := by
    refine hx.1.restrict_scalars ?_
    intro r s e
    apply hinj
    simpa [Algebra.algebraMap_eq_smul_one] using e
  have h1 : Module.finrank O (lieSub C D τ) = a := by
    rw [← hx.2, finrank_span_eq_card hliO, Fintype.card_fin]
  have h2 : Module.finrank O ↥(D.Lie ⊓ D.Tsub τ) = Module.finrank O (lieSub C D τ) :=
    (Submodule.equivMapOfInjective _ hincl _).finrank_eq
  unfold Datum.lieRank
  rw [h2, h1]

theorem span_eigPart_top (D : Datum ε h Λ) (τ : Λ →+* O)
    (hind : iSupIndep (fun σ : Λ →+* O => eig C (actT D) σ))
    (htop : (⨆ σ : Λ →+* O, eig C (actT D) σ) = ⊤) {n : ℕ} (u : Fin n → Fin h → C)
    (hu : Submodule.span O (Set.range u) = eigPart C (actT D) τ ⊤) (hue : ∀ i, u i ∈ eig C (actT D) τ) :
    Submodule.span C (Set.range u) = eig C (actT D) τ := by
  set S := Submodule.span C (Set.range u) with hSdef
  set R := ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C (actT D) σ.1 with hRdef
  have hSle : S ≤ eig C (actT D) τ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hue i
  have hdisj : Disjoint (eig C (actT D) τ) R :=
    (hind τ).mono_right (iSup_le fun σ => le_iSup₂_of_le (f := fun j (_ : j ≠ τ) => eig C (actT D) j) σ.1 σ.2 le_rfl)
  have htop' : eig C (actT D) τ ⊔ R = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← htop]
    refine iSup_le fun σ => ?_
    by_cases hσ : σ = τ
    · subst hσ
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup (fun σ : {σ : Λ →+* O // σ ≠ τ} => eig C (actT D) σ.1) ⟨σ, hσ⟩)
  have hS : ∀ z, z ∈ eigPart C (actT D) τ ⊤ → z ∈ S := by
    intro z hz
    rw [← hu] at hz
    exact Submodule.span_le_restrictScalars O C _ hz
  have hall : (⊤ : Submodule C (Fin h → C)) ≤ S ⊔ R := by
    rw [← (Pi.basisFun C (Fin h)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hej : (Pi.basisFun C (Fin h) j) ∈ eig C (actT D) τ ⊔ R := by
      rw [htop']
      trivial
    obtain ⟨y, hy, r, hr, hyr⟩ := Submodule.mem_sup.1 hej
    have hy' : y ∈ eigPart C (actT D) τ ⊤ := by
      refine Submodule.mem_inf.2 ⟨hy, ?_⟩
      refine Submodule.mem_sup.2 ⟨Pi.basisFun C (Fin h) j, ⟨Pi.single j 1, trivial, ?_⟩, -r,
        Submodule.neg_mem _ hr, by rw [← hyr]; abel⟩
      funext k
      by_cases hk : k = j
      · subst hk
        simp [incl_apply']
      · simp [incl_apply', Pi.single_apply, hk]
    exact Submodule.mem_sup.2 ⟨y, hS y hy', r, hr, hyr⟩
  refine le_antisymm hSle fun z hz => ?_
  have hz' : z ∈ (S ⊔ R) ⊓ eig C (actT D) τ := ⟨hall trivial, hz⟩
  rwa [sup_inf_assoc_of_le R hSle, hdisj.symm.eq_bot, sup_bot_eq] at hz'

end Parts

theorem lieRank_add_card_and_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) (a b : ℕ) (x : Fin a → Fin h → C) (w : Fin a → Fin h → C) (n : Fin b → Fin h → C), IsBasisOf C (lieSub C D τ) x → IsBasisOf C (wQuot C D τ) w → IsBasisOf C (alQuot C D τ) n → a = D.lieRank τ ∧ a + b = N ∧ ∀ i, ∃ y : eig C (actH D) τ, bC C D y = x i := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D τ a b x w n hx hw hn
  obtain ⟨⟨hindT, htopT, hdimT⟩, ⟨hindH, htopH, hdimH⟩⟩ :=
    GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ N h hh D
  refine ⟨card_eq_lieRank hv.hom_inj D τ x hx, ?_, ?_⟩
  · obtain ⟨u, -, -, hu, -⟩ := GlobalTheory.T.dvr_determinant_product_orders p C v O hv ε hε Λ a b h D τ w n hw hn
    have hspan := span_eigPart_top D τ hindT htopT (fun i => (u i : Fin h → C)) hu.2
      (fun i => (u i).2)
    have e := finrank_span_eq_card hu.1
    rw [hspan, hdimT τ, Fintype.card_fin] at e
    exact e.symm
  · intro i
    have hint := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
    have hX : ∀ l, D.G.map (WittVector.fontaineTheta O p) * actH D l =
        actT D l * D.G.map (WittVector.fontaineTheta O p) := by
      intro l
      have e' := congrArg (fun M => M.map (WittVector.fontaineTheta O p)) (hint.2.2.1 l)
      simp only [Matrix.map_mul] at e'
      unfold actH actT
      rw [e']
      simp only [rhoTA, Matrix.map_map]
      rfl
    have hmap := (GlobalTheory.T.intertwiner_maps_eigenspaces C O Λ h (actH D) (actT D)
      (D.G.map (WittVector.fontaineTheta O p)) hX).2 htopH hindT τ
    have hbC : bC C D = Matrix.toLin' ((D.G.map (WittVector.fontaineTheta O p)).map (algebraMap O C)) :=
      rfl
    have hxi : x i ∈ lieSub C D τ := hx.2 ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨l, ⟨hlL, hlT⟩, hl⟩ := Submodule.mem_map.1 hxi
    obtain ⟨m, rfl⟩ := hlL
    have hT : incl C h (D.bb m) ∈ eig C (actT D) τ := by
      refine incl_mem_eig _ _ _ fun c => ?_
      have := (Submodule.mem_iInf _).1 hlT c
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at this
      exact this
    have hR : incl C h (D.bb m) ∈ LinearMap.range (bC C D) := by
      refine ⟨incl C h m, ?_⟩
      funext k
      rw [hbC, Matrix.toLin'_apply, incl_apply', incl_apply']
      show _ = algebraMap O C ((D.G.map (WittVector.fontaineTheta O p) *ᵥ m) k)
      rw [RingHom.map_mulVec]
      rfl
    rw [hbC] at hR
    have hmem := hmap ▸ (Submodule.mem_inf.2 ⟨hR, hT⟩)
    obtain ⟨y, hy, hyeq⟩ := Submodule.mem_map.1 hmem
    exact ⟨⟨y, hy⟩, by rw [hbC]; exact hyeq.trans hl⟩

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyBaseChangeCoprodBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.BcCoprod

theorem bc_map_fst {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {V U : Over S} (g : V ⟶ U) :
    (bc p).map g ≫ (pullback.fst p (sch.map U.hom) : (bc p).obj U ⟶ E) = pullback.fst p (sch.map V.hom) := by
  simp only [bc, pullback.map]
  exact pullback.lift_fst _ _ _

theorem bc_map_snd {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {V U : Over S} (g : V ⟶ U) :
    (bc p).map g ≫ (pullback.snd p (sch.map U.hom) : (bc p).obj U ⟶ _) = pullback.snd p (sch.map V.hom) ≫ sch.map g.left := by
  simp only [bc, pullback.map]
  exact pullback.lift_snd _ _ _

theorem isPullback_bc {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {V U : Over S} (g : V ⟶ U) :
    IsPullback ((bc p).map g) (pullback.snd p (sch.map V.hom)) (pullback.snd p (sch.map U.hom)) (sch.map g.left) := by
  have h2 : sch.map g.left ≫ sch.map U.hom = sch.map V.hom := by
    rw [← sch.map_comp, Over.w g]
  have outer : IsPullback ((bc p).map g ≫ (pullback.fst p (sch.map U.hom) : (bc p).obj U ⟶ E))
      (pullback.snd p (sch.map V.hom)) p (sch.map g.left ≫ sch.map U.hom) := by
    rw [bc_map_fst p g, h2]
    exact IsPullback.of_hasPullback p (sch.map V.hom)
  exact IsPullback.of_right outer (bc_map_snd p g) (IsPullback.of_hasPullback p (sch.map U.hom))

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (U : Over S) (ι : Type) (V : ι → Over S) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U.left (fun i => (j i).left)) → ∀ n : ℤ, Function.Bijective (fun (x : H R ((bc p).obj U) F n) (i : ι) => pull R ((bc p).map (j i)) F n x) := by
  intro R _ F S E p U ι V j hc n
  refine GlobalTheory.T.etaleSpaceCohomology_levelwise_coproduct_bijective R F ((bc p).obj U) ι (fun i => (bc p).obj (V i)) (fun i => (bc p).map (j i)) (fun k => ?_) n
  refine GlobalTheory.T.freeEtaleSheaf_presheaf_over_coproduct_eq_sum R U.left ι (fun i => (V i).left) (fun i => (j i).left) hc (((bc p).obj U).obj k)
    ((pullback.snd p (sch.map U.hom)).app k) (fun i => ((bc p).obj (V i)).obj k)
    (fun i => ((bc p).map (j i)).app k) (fun i => (pullback.snd p (sch.map (V i).hom)).app k) (fun i => ?_)
  exact (isPullback_bc p (j i)).map ((evaluation _ _).obj k)

end GlobalTheory.EtC.BcCoprod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsQuaternionNormOneReEqStatement
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_exists_quaternion_norm_one_re_eq : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), ∀ t ∈ v.adicCompletionIntegers F, ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b], nrm u = 1 ∧ u.re = t ∧ u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧ u.imK ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq | exact GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq | (intros; apply GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoinducedSheafInjectiveResolutionFreeExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.EtC.coindRes_exists : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R) [Injective J], (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → ∃ (C : Cx R) (ε : sgl ((restr φ).obj ((coind φ).obj J)) ⟶ C), C.IsStrictlyGE 0 ∧ (∀ t, Injective (C.X t)) ∧ QuasiIso ε ∧ ∀ (P : PSh) (n : ℤ), 0 < n → Subsingleton (CohomologyClass (sgl ((free R).obj P)) C n) := by
  intro R S _ _ φ J _ hJ
  haveI := GlobalTheory.T.etaleCoinductionComplexAugmentation_quasiIso R S φ J hJ
  let I : InjectiveResolution ((restr φ).obj ((coind φ).obj J)) :=
    { cocomplex := coindCx φ J
      injective := fun n => GlobalTheory.T.injective_etaleSheafOfLinearMapsFromModule R J ((scalarsRes φ).complex.X n)
      ι := coindAug φ J }
  refine ⟨I.cochainComplex, I.ι', inferInstance, inferInstance, inferInstance, ?_⟩
  intro P n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ x : CohomologyClass (sgl ((free R).obj P)) I.cochainComplex ((k : ℤ) + 1), x = 0 by
    rw [h x, h y]
  intro x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective α ((k : ℤ) + 1) (zero_add _) ((k : ℤ) + 1 + 1) rfl
  rw [CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (k : ℤ) rfl]
  have hex : ∀ b, ((scalarsRes φ).complex.d (k + 1) k).hom b = 0 → ∃ a, ((scalarsRes φ).complex.d (k + 2) (k + 1)).hom a = b := by
    intro b hb
    exact ((ShortComplex.moduleCat_exact_iff _).1 ((scalarsRes φ).exact_succ k)) b hb
  have hd1 := I.cochainComplex_d ((k : ℤ) + 1) ((k : ℤ) + 1 + 1) (k + 1) (k + 2) (by simp) (by push_cast; ring)
  rw [hd1] at hf
  have h2 : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫ I.cocomplex.d (k + 1) (k + 2) = 0 := by
    rw [← cancel_mono (I.cochainComplexXIso ((k : ℤ) + 1 + 1) (k + 2) (by push_cast; ring)).inv]
    simpa using hf
  have hf' : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫
      (homSh J).map ((scalarsRes φ).complex.d (k + 2) (k + 1)).op = 0 := by
    rw [← coindCx_d]
    exact h2
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_lift_etaleSheafOfLinearMaps_exact R J ((free R).obj P) (hJ P) _ _ _ _ _ hex _ hf'
  refine ⟨g ≫ (I.cochainComplexXIso (k : ℤ) k rfl).inv, ?_⟩
  rw [I.cochainComplex_d (k : ℤ) ((k : ℤ) + 1) k (k + 1) rfl (by simp)]
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  have hg' : g ≫ I.cocomplex.d k (k + 1) = f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom := by
    rw [← hg, ← coindCx_d]
    rfl
  erw [← Category.assoc, hg', Category.assoc, Iso.hom_inv_id, Category.comp_id]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectingCocycleHypercohomologyLesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_connecting_cocycle_hypercohomology_les : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
  ∃ z : Cocycle (res R S.X₃) (res R S.X₁) 1,
    (∀ (K : Cx R) (n : ℤ),
      Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
      Function.Exact (HK.post R K S.g n) (HK.ext R K z n (n + 1) rfl) ∧
      Function.Exact (HK.ext R K z n (n + 1) rfl) (HK.post R K S.f (n + 1))) ∧
    ∃ s : ℤˣ, ∀ (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
      S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
      ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug S.X₃)) z (zero_add 1)) = s • CohomologyClass.mk w := by
  first | (exact @GlobalTheory.EtC.LesChar.exists_connecting_cocycle) | (exact GlobalTheory.EtC.LesChar.exists_connecting_cocycle) | (intros; apply GlobalTheory.EtC.LesChar.exists_connecting_cocycle  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemRightTranslateMemIdentityComponentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_rightTranslate_mem_identityComponent : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), (η[G]).left (IsLocalRing.closedPoint k) ∈ U → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → ∃ z : G.left, z ∈ U ∧ (𝟙 G * (toUnit G ≫ y) : G ⟶ G).left z ∈ U := by
  first | exact @GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent | exact GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent | (intros; apply GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent <;> assumption)
end

