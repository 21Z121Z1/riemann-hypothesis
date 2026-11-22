import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0102
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0403
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactLieAction

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.CTFin.CapFactor

theorem two_sum (n : Fin 2 → ℕ) : ∑ i, n i = n 0 + n 1 := Fin.sum_univ_two n

theorem std_zero (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1) (i : Fin (n 0)) :
    stdBlocks n h ⟨0, i⟩ = Fin.castAdd (n 1) i := by
  apply Fin.ext
  refine (stdBlocks_val n h 0 i).trans ?_
  simp

theorem std_one (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1) (i : Fin (n 1)) :
    stdBlocks n h ⟨1, i⟩ = Fin.natAdd (n 0) i := by
  apply Fin.ext
  refine (stdBlocks_val n h 1 i).trans ?_
  simp

theorem modExp_zero (n : Fin 2 → ℕ) : modExp (fun i => Fin (n i)) 0 = n 1 := by
  have h1 : (Finset.univ.filter fun b : Fin 2 => (0 : Fin 2) < b) = {1} := by decide
  simp [modExp, h1]

theorem modExp_one (n : Fin 2 → ℕ) : modExp (fun i => Fin (n i)) 1 = -(n 0 : ℤ) := by
  have h1 : (Finset.univ.filter fun b : Fin 2 => (1 : Fin 2) < b) = ∅ := by decide
  simp [modExp, h1, Finset.sum_filter]

theorem exists_unip_of_mem {R : Type} [CommRing R] (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1)
    {v : GL (Fin (n 0 + n 1)) R} (hv : v ∈ unipRad R (stdBlocks n h)) :
    ∃ x : BlockIx (n 0 + n 1) (n 0) → R, v = unip x := by
  obtain ⟨hp, hd⟩ := mem_unipRad.1 hv
  have hp' := mem_parab_iff.1 hp
  have A : ∀ i j : Fin (n 0), (v : Matrix _ _ R) (Fin.castAdd (n 1) i) (Fin.castAdd (n 1) j) =
      (1 : Matrix (Fin (n 0)) (Fin (n 0)) R) i j := by
    intro i j
    have := hd 0 i j
    rwa [std_zero, std_zero] at this
  have B : ∀ i j : Fin (n 1), (v : Matrix _ _ R) (Fin.natAdd (n 0) i) (Fin.natAdd (n 0) j) =
      (1 : Matrix (Fin (n 1)) (Fin (n 1)) R) i j := by
    intro i j
    have := hd 1 i j
    rwa [std_one, std_one] at this
  have C : ∀ (i : Fin (n 1)) (j : Fin (n 0)), (v : Matrix _ _ R) (Fin.natAdd (n 0) i) (Fin.castAdd (n 1) j) = 0 := by
    intro i j
    have := hp' 1 0 i j (by decide)
    rwa [std_one, std_zero] at this
  refine ⟨fun p => (v : Matrix (Fin (n 0 + n 1)) (Fin (n 0 + n 1)) R) p.1.1 p.1.2, Units.ext ?_⟩
  change (v : Matrix (Fin (n 0 + n 1)) (Fin (n 0 + n 1)) R) = 1 + nilM _
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have : ¬ (((Fin.castAdd (n 1) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.castAdd (n 1) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_castAdd]; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, add_zero, A, Matrix.one_apply, Fin.castAdd_inj]
  · have : (((Fin.castAdd (n 1) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.natAdd (n 0) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
    have hne : (Fin.castAdd (n 1) i : Fin (n 0 + n 1)) ≠ Fin.natAdd (n 0) j := by
      intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_pos this, Matrix.one_apply, if_neg hne, zero_add]
  · have : ¬ (((Fin.natAdd (n 0) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.castAdd (n 1) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
    have hne : (Fin.natAdd (n 0) i : Fin (n 0 + n 1)) ≠ Fin.castAdd (n 1) j := by
      intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, Matrix.one_apply, if_neg hne, add_zero, C]
  · have : ¬ (((Fin.natAdd (n 0) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.natAdd (n 0) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_natAdd]; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, add_zero, B, Matrix.one_apply, Fin.natAdd_inj]

def levPair {R : Type} [CommRing R] {n : Fin 2 → ℕ} (g : GL (Fin (n 0)) R × GL (Fin (n 1)) R) :
    ∀ i : Fin 2, GL (Fin (n i)) R
  | ⟨0, _⟩ => g.1
  | ⟨1, _⟩ => g.2

theorem lev_eq_leviEmb {R : Type} [CommRing R] (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1)
    (g : GL (Fin (n 0)) R × GL (Fin (n 1)) R) :
    lev R (n 0) (n 1) g = leviEmb R (stdBlocks n h) (levPair g) := by
  have p0 : ∀ i : Fin (n 0), two (stdSum (rfl : n 0 + n 1 = n 0 + n 1)) ⟨false, i⟩ = stdBlocks n h ⟨0, i⟩ := fun i => by
    rw [std_zero, two_false]; exact Fin.ext (by simp)
  have p1 : ∀ i : Fin (n 1), two (stdSum (rfl : n 0 + n 1 = n 0 + n 1)) ⟨true, i⟩ = stdBlocks n h ⟨1, i⟩ := fun i => by
    rw [std_one, two_true]; exact Fin.ext (by simp)
  have key : ∀ (a b : Fin 2) (i : Fin (n a)) (j : Fin (n b)),
      (lev R (n 0) (n 1) g : Matrix _ _ R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) =
      (leviEmb R (stdBlocks n h) (levPair g) : Matrix _ _ R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) := by
    refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun i j => ?_, fun i j => ?_⟩,
      Fin.forall_fin_two.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
    · rw [leviEmb_apply_same, ← p0, ← p0]
      exact leviEmb_apply_same R (two _) (leviTwo R _ _ g) false i j
    · rw [leviEmb_apply_ne R _ _ (a := 0) (b := 1) (by decide), ← p0, ← p1]
      exact leviEmb_apply_ne R (two _) (leviTwo R _ _ g) (a := false) (b := true) (by simp) i j
    · rw [leviEmb_apply_ne R _ _ (a := 1) (b := 0) (by decide), ← p0, ← p1]
      exact leviEmb_apply_ne R (two _) (leviTwo R _ _ g) (a := true) (b := false) (by simp) i j
    · rw [leviEmb_apply_same, ← p1, ← p1]
      exact leviEmb_apply_same R (two _) (leviTwo R _ _ g) true i j
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks n h).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks n h).surjective j
  exact key a b i j

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem qdet_mem {A : Type} [Ring A] [Algebra ℂ A] {a : ℕ} (S : Subalgebra ℂ A) (X : Fin a → Fin a → A)
    (hX : ∀ i j, X i j ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  have := map_qdet S.val (fun i j => (⟨X i j, hX i j⟩ : S)) u
  simp only [Subalgebra.coe_val] at this
  rw [← this]
  exact (Formalism.REAL.qdet _ _ : S).2

theorem Eop_commute_blocks (r s : ℕ) (τ : E →+* ℂ) (i j : Fin r) (k l : Fin s) :
    Commute (Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j))
      (Eop (a := r + s) τ (Fin.natAdd r k) (Fin.natAdd r l)) := by
  have h := glRel_Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j) (Fin.natAdd r k) (Fin.natAdd r l)
  have h1 : (Fin.castAdd s j : Fin (r + s)) ≠ Fin.natAdd r k := by
    intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
  have h2 : (Fin.natAdd r l : Fin (r + s)) ≠ Fin.castAdd s i := by
    intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
  rw [if_neg h1, if_neg h2, sub_zero] at h
  exact sub_eq_zero.1 h

theorem capR_commute_capS (r s : ℕ) (τ : E →+* ℂ) (u v : ℂ) : Commute (capR r s τ u) (capS r s τ v) := by
  let T : Set (Module.End ℂ (Sm E (r + s))) :=
    Set.range fun kl : Fin s × Fin s => Eop (a := r + s) τ (Fin.natAdd r kl.1) (Fin.natAdd r kl.2)
  have h1 : capR r s τ u ∈ Subalgebra.centralizer ℂ T := by
    refine qdet_mem _ _ (fun i j => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨kl, rfl⟩
    exact (Eop_commute_blocks r s τ i j kl.1 kl.2).symm.eq
  have h2 : capS r s τ v ∈ Subalgebra.centralizer ℂ {capR r s τ u} := by
    refine qdet_mem _ _ (fun k l => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact ((Subalgebra.mem_centralizer_iff ℂ).1 h1 _ ⟨(k, l), rfl⟩).symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 h2 _ rfl)

theorem capelli_levi_factorization (n : Fin 2 → ℕ) (τ : E →+* ℂ) (u : ℂ) (F : Sm E (n 0 + n 1))
    (hF : ∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) (g : GA E (n 0 + n 1)), F.1 (unip x * g) = F.1 g)
    (m : GA E (n 0) × GA E (n 1)) :
    (cap (a := n 0 + n 1) τ u F).1 (lev (Ad E) (n 0) (n 1) m) =
      (capS (n 0) (n 1) τ (u + (n 0 : ℂ) / 2) (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) F)).1
        (lev (Ad E) (n 0) (n 1) m) := by
  have h : ∑ i, n i = n 0 + n 1 := two_sum n
  let S : Subalgebra ℂ (Module.End ℂ (Sm E (n 0 + n 1))) :=
    Algebra.adjoin ℂ (Set.range fun pq : Fin (n 0 + n 1) × Fin (n 0 + n 1) => Eop τ pq.1 pq.2)
  have hSE : ∀ p q, Eop τ p q ∈ S := fun p q => Algebra.subset_adjoin ⟨(p, q), rfl⟩
  have hSL : S ≤ GlobalTheory.SpehInfChar.leftInvAlg (unipRad (Ad E) (stdBlocks n h)) :=
    Algebra.adjoin_le (by rintro _ ⟨pq, rfl⟩; exact GlobalTheory.SpehInfChar.Eop_mem_leftInvAlg _ τ pq.1 pq.2)
  let X : Fin (n 0 + n 1) → Fin (n 0 + n 1) → S := fun p q => ⟨Eop τ p q, hSE p q⟩
  have hX : Formalism.REAL.GlRel X := fun a b c' d => Subtype.ext (by
    have := glRel_Eop (a := n 0 + n 1) τ a b c' d
    split_ifs at this ⊢ <;> simpa [X] using this)
  have key := GlobalTheory.SpehInfChar.qdet_sub_blocks_mem S n h X hX u
  have hB0 : Formalism.REAL.qdet (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩))
      (u + ((n 0 : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) 0 : ℂ) / 2) = capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) := by
    have e1 : (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩)) =
        fun p q => Eop (a := n 0 + n 1) τ (Fin.castAdd (n 1) p) (Fin.castAdd (n 1) q) := by
      funext p q
      rw [std_zero, std_zero]
    rw [e1, modExp_zero, capR]
    congr 1
    push_cast
    ring
  have hB1 : Formalism.REAL.qdet (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩))
      (u + ((n 1 : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) 1 : ℂ) / 2) = capS (n 0) (n 1) τ (u + (n 0 : ℂ) / 2) := by
    have e1 : (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩)) =
        fun p q => Eop (a := n 0 + n 1) τ (Fin.natAdd (n 0) p) (Fin.natAdd (n 0) q) := by
      funext p q
      rw [std_one, std_one]
    rw [e1, modExp_one, capS]
    congr 1
    push_cast
    ring
  have hval : S.val (List.ofFn fun i : Fin 2 => Formalism.REAL.qdet (fun p q : Fin (n i) => X (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod =
      capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) * capS (n 0) (n 1) τ (u + (n 0 : ℂ) / 2) := by
    rw [map_list_prod, List.map_ofFn, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    simp only [Function.comp_apply, List.prod_cons, List.prod_nil, mul_one, Fin.succ_zero_eq_one]
    rw [← hB0, ← hB1, map_qdet, map_qdet]
    rfl
  have hcap : S.val (Formalism.REAL.qdet X (u + (((n 0 + n 1 : ℕ) : ℂ) - 1) / 2)) = cap τ u := by
    rw [map_qdet]
    rfl
  have hψ : ∀ v ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, F.1 (v * g) = F.1 g := fun v hv g => by
    obtain ⟨x, rfl⟩ := exists_unip_of_mem n h hv
    exact hF x g
  rw [lev_eq_leviEmb n h m]
  set ℓ := leviEmb (Ad E) (stdBlocks n h) (levPair m) with hℓ
  let L : S →ₗ[ℂ] ℂ :=
    { toFun := fun w => ((w : Module.End ℂ (Sm E (n 0 + n 1))) F).1 ℓ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : Submodule.span ℂ {y : S | ∃ (p q : Fin (n 0 + n 1)) (w : S), blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} ≤
      LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, q, w, hpq, rfl⟩
    change (Eop τ p q ((w : Module.End ℂ (Sm E (n 0 + n 1))) F)).1 ℓ = 0
    exact GlobalTheory.SpehInfChar.Eop_leviEmb_eq_zero E n h _ (hSL w.2 F hψ) τ p q hpq _
  have h1 := hker key
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
  have hL : ∀ w : S, L w = ((S.val w) F).1 ℓ := fun _ => rfl
  rw [hL, hL, hcap, hval] at h1
  rw [h1, (capR_commute_capS (n 0) (n 1) τ _ _).eq]
  rfl

theorem cap_levi : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ)
    (F : Sm E (r + s)), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) →
    ∀ m : GA E r × GA E s, (cap (a := r + s) τ u F).1 (lev (Ad E) r s m) =
      (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) F)).1 (lev (Ad E) r s m) := by
  intro E _ _ _ r s τ u F hF m
  exact capelli_levi_factorization ![r, s] τ u F hF m

end GlobalTheory.CompanionTheory.CTFin.CapFactor

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirEqOfSingularWeightVector
section
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

theorem cas_mul_sub_mem_Jp (y : U n) (τ : Fin n → ℂ)
    (hd : ∀ k, e (k, k) * y - τ k • y ∈ Jp n)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → e a * y ∈ Jp n) :
    Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * y - casC τ • y ∈ Jp n := by
  have key : ∀ a b : Fin n, e (a, b) * e (b, a) * y -
      ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y ∈ Jp n := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · have hc : e (a, b) * e (b, a) - e (b, a) * e (a, b) = e (a, a) - e (b, b) := by
        simpa using e_mul_sub_mul (a, b) (b, a)
      have hcomm : e (a, b) * e (b, a) = e (b, a) * e (a, b) + (e (a, a) - e (b, b)) := by
        rw [← hc]; abel
      have hval : e (a, b) * e (b, a) * y -
          ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y =
          e (b, a) * (e (a, b) * y) + (e (a, a) * y - τ a • y) - (e (b, b) * y - τ b • y) := by
        rw [if_neg h.ne, if_pos h, hcomm, zero_add, sub_smul]
        simp only [add_mul, sub_mul, mul_assoc]
        abel
      rw [hval]
      exact Submodule.sub_mem _ (Submodule.add_mem _ (mul_mem_Jp _ (hu _ h)) (hd a)) (hd b)
    · subst h
      have hval : e (a, a) * e (a, a) * y -
          ((if a = a then τ a ^ 2 else 0) + (if a < a then τ a - τ a else 0)) • y =
          e (a, a) * (e (a, a) * y - τ a • y) + τ a • (e (a, a) * y - τ a • y) := by
        simp only [if_true, lt_irrefl, if_false, add_zero, mul_sub, mul_smul_comm, smul_sub,
          smul_smul, mul_assoc, pow_two]
        abel
      rw [hval]
      exact Submodule.add_mem _ (mul_mem_Jp _ (hd a)) (Submodule.smul_mem _ _ (hd a))
    · have hval : e (a, b) * e (b, a) * y -
          ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y =
          e (a, b) * (e (b, a) * y) := by
        rw [if_neg h.ne', if_neg h.not_gt]
        simp [mul_assoc]
      rw [hval]
      exact mul_mem_Jp _ (hu _ h)
  have hsum : casC τ = ∑ a, ∑ b : Fin n,
      ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) := by
    simp only [casC, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hval : Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * y - casC τ • y =
      ∑ a, ∑ b : Fin n, (e (a, b) * e (b, a) * y -
        ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y) := by
    rw [hsum]
    simp only [Formalism.REAL.Cas, Finset.sum_mul, Finset.sum_smul, Finset.sum_sub_distrib]
  rw [hval]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => key a b

theorem cas_mul_comm (x : U n) :
    x * Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) =
      Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * x := by
  have hz : Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) ∈ Subalgebra.center ℂ (U n) :=
    mem_center_of_commute_e fun a => by
      obtain ⟨c, d⟩ := a
      exact (Formalism.FourierDecayAlt.P.WigCas.cas_comm (glRel_e n) c d).symm
  exact (Subalgebra.mem_center_iff.1 hz) x

theorem upper_e_mem_Jp (a : Fin n × Fin n) (ha : IsUpper a) : e a ∈ Jp n :=
  vermaIdeal_le_Jp (nPlusU_le_vermaIdeal _ (Submodule.subset_span ⟨1, a, ha, one_mul _⟩))

theorem e_sub_rho_mem_Jp (u : U n) (k : Fin n) : u * e (k, k) - rhoVec n k • u ∈ Jp n := by
  have h := vermaIdeal_le_Jp (mul_e_sub_mem_vermaIdeal (rhoVec n) u k)
  have hv : u * (e (k, k) - algebraMap ℂ (U n) (rhoVec n k)) = u * e (k, k) - rhoVec n k • u := by
    rw [mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  rwa [hv] at h

theorem casC_rho_add_eq (μ : Fin n → ℤ) (x : U n) (hw : IsAdW μ x)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) (hx : x ∉ Jp n) :
    casC (fun k => rhoVec n k + (μ k : ℂ)) = casC (rhoVec n) := by
  have h1 := cas_mul_sub_mem_Jp (1 : U n) (rhoVec n)
    (fun k => by simpa using e_sub_rho_mem_Jp (1 : U n) k) (fun a ha => by
      rw [mul_one]; exact upper_e_mem_Jp a ha)
  have h2 := cas_mul_sub_mem_Jp x (fun k => rhoVec n k + (μ k : ℂ)) (fun k => by
    have hv : e (k, k) * x - (rhoVec n k + (μ k : ℂ)) • x = x * e (k, k) - rhoVec n k • x := by
      have := hw k
      rw [add_smul, ← this]; abel
    rw [hv]; exact e_sub_rho_mem_Jp x k) hu
  have h3 := mul_mem_Jp x h1
  have hv : x * (Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * 1 - casC (rhoVec n) • (1 : U n)) -
      (Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * x -
        casC (fun k => rhoVec n k + (μ k : ℂ)) • x) =
      (casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n)) • x := by
    rw [mul_one, mul_sub, cas_mul_comm, mul_smul_comm, mul_one, sub_smul]; abel
  have h4 := Submodule.sub_mem _ h3 h2
  rw [hv] at h4
  by_contra hne
  apply hx
  have hc : casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n) ≠ 0 := sub_ne_zero.2 hne
  have := Submodule.smul_mem _ (casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n))⁻¹ h4
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end GlobalTheory.CompanionTheory.PresRho
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentredSegmentSquareIntegrable
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SegLink

theorem one_le_deg_of_isLSeg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {Δ : Segment k} {y : IrrGL k} (hL : IsLSeg Δ y.rep) : 1 ≤ y.1 := by
  obtain ⟨hd, -⟩ := hL
  have hterm : ∀ a, (Δ.term a).fst = Δ.d := fun a => rfl
  rw [← hd]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.mul_pos Δ.len_pos Δ.d_pos

theorem norm_top_eq (r A : ℝ) (d d0 l0 l1 m : ℕ) (h : d0 = d) :
    (r * (A ^ l1) ^ d) ^ l0 * (A ^ d0) ^ m = r ^ l0 * A ^ (d * (l0 * l1 + m)) := by
  subst h
  ring

theorem centredSegSqInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Zls.CasselmanSuffSq k → GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → Zz.CentredSegSqInt k := by
  intro k _ _ _ _ hCas hIA hLJ Δ y hL hU
  have hN : 1 ≤ y.1 := one_le_deg_of_isLSeg hL
  have hmax : Zls.MaxExpStrict y.rep := by
    intro x hd hpos hjm t ht c hc
    obtain ⟨Γ, ⟨hlen, hfirst⟩, hΓ⟩ := GlobalTheory.T.segment_jacquet_two_factor_split k Δ y.1 _ y.rep hLJ hL x hd hpos hjm
    obtain ⟨hα0, hα1, hnorm⟩ := GlobalTheory.T.contracting_unit_abs_pow_bounds k t ht
    obtain ⟨c0, hc0⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k Δ.first.fst _ Δ.first.rep Δ.first.snd.rep.smooth
      Δ.first.snd.rep.irr (hIA k _ _ _ Δ.first.snd.rep.smooth Δ.first.snd.rep.irr) t
    obtain ⟨cy, hcy⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k y.fst _ y.rep y.snd.rep.smooth y.snd.rep.irr
      (hIA k _ _ _ y.snd.rep.smooth y.snd.rep.irr) t
    have hprod := GlobalTheory.T.jacquet_two_factor_central_character_mul k y.fst _ y.rep x hd hjm t cy (c 0) (c 1) hcy (hc 0) (hc 1)
    have hcy1 : ‖cy‖ = 1 := hU t cy hcy
    have hy1 := hU t _ (GlobalTheory.T.segment_rep_central_character_formula k Δ y hL t c0 hc0)
    rw [norm_mul, norm_pow, norm_pow, hnorm, ← pow_mul] at hy1
    have hr : 0 < ‖c0‖ := by
      rcases (norm_nonneg c0).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, zero_pow (Nat.pos_iff_ne_zero.mp Δ.len_pos), zero_mul] at hy1
        exact zero_ne_one hy1
    have hlen2 : (Γ 0).len + (Γ 1).len = Δ.len := by rw [← hlen, Fin.sum_univ_two]
    rw [← hlen2] at hy1
    have hb0 : Zc.below Γ 0 = (Γ 1).len := by
      simp [Zc.below, Finset.sum_filter, Fin.sum_univ_two]
    have hf0 : (Γ 0).first.fst = Δ.first.fst := by rw [hfirst 0]; rfl
    have hG0 : Zl.ScalarBy (Γ 0).first t
        (c0 * ↑((GlobalTheory.SmGL.absPow k ↑(Zc.below Γ 0)) t) ^ Δ.first.fst) := by
      rw [hfirst 0]
      exact GlobalTheory.T.central_character_twist_pow_degree k Δ.first t c0 _ hc0
    have he0 := GlobalTheory.T.central_character_eq_of_scalar k (x 0) t _ _ (hc 0) (GlobalTheory.T.segment_rep_central_character_formula k (Γ 0) (x 0) (hΓ 0) t _ hG0)
    have hn0 : ‖c 0‖ = ‖c0‖ ^ (Γ 0).len * GlobalTheory.SplitWeil.nabs k t ^
        (Δ.first.fst * ((Γ 0).len * (Γ 1).len + (Γ 0).len * ((Γ 0).len - 1) / 2)) := by
      rw [he0, norm_mul, norm_pow, norm_mul, norm_pow, norm_pow, hnorm, hnorm, hb0]
      exact norm_top_eq _ _ _ _ _ _ _ hf0
    refine ⟨?_, ?_⟩
    · intro j hj
      have hj0 : j = 0 := Fin.ext (by omega)
      subst hj0
      have hp : (∏ i ∈ Finset.univ.filter (fun i : Fin 2 => i ≤ 0), ‖c i‖) = ‖c 0‖ := by
        simp [Finset.prod_filter, Fin.prod_univ_two]
      rw [hp, hn0]
      exact GlobalTheory.T.real_pow_partial_segment_lt_one _ _ _ _ _ hα0 hα1 hr Δ.d_pos (Γ 0).len_pos (Γ 1).len_pos hy1
    · rw [Fin.prod_univ_two, ← norm_mul, hprod, hcy1]
  exact @hCas y.1 _ _ _ y.rep hN y.snd.rep.smooth y.snd.rep.irr (fun t c hc => hU t c hc) hmax

end GlobalTheory.CompanionTheory.SegLink
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedPointsCountComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
namespace GlobalTheory.CompanionTheory.KoszulCount

theorem cxPts_eq_of_pt_eq {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {y y' : CxPts p (RingHom.id ℂ)}
    (h : y.1 (closedPoint ℂ) = y'.1 (closedPoint ℂ)) : y = y' := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := y.1 (closedPoint ℂ)) (U := ⊤) trivial
  have hy : y ∈ ptsIn p (RingHom.id ℂ) U := mem_ptsIn.2 hx
  have hy' : y' ∈ ptsIn p (RingHom.id ℂ) U := mem_ptsIn.2 (h ▸ hx)
  have hv : ∀ g : Γ(X, U), ev p (RingHom.id ℂ) U g y = 0 → ev p (RingHom.id ℂ) U g y' = 0 := by
    intro g hg
    by_contra hne
    have h₁ := (mem_ptsIn_basicOpen hy' g).2 hne
    have h₂ : y ∈ ptsIn p (RingHom.id ℂ) (X.basicOpen g) := mem_ptsIn.2 (h ▸ mem_ptsIn.1 h₁)
    exact (mem_ptsIn_basicOpen hy g).1 h₂ hg
  refine Subtype.ext (GlobalTheory.Points.ext_of_valR hU hy hy' fun f => ?_)
  have e₀ : ev p (RingHom.id ℂ) U
      (f - ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (ev p (RingHom.id ℂ) U f y)) y = 0 := by
    rw [ev_eq hy, map_sub, ← ev_eq hy, ← ev_eq hy, ev_algX hy]
    simp
  have e₁ := hv _ e₀
  rw [ev_eq hy', map_sub, ← ev_eq hy', ← ev_eq hy', ev_algX hy'] at e₁
  exact (sub_eq_zero.1 e₁).symm

theorem exists_cxPts_pt_eq {X : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    ∃ y : CxPts p (RingHom.id ℂ), y.1 (closedPoint ℂ) = x := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  obtain ⟨⟨y, -, hs⟩, -⟩ :=
    GlobalTheory.SpecialisationPts.nonempty_and_isPreconnected X p inferInstance U hU x hxU
  exact ⟨y, (hs.mem_closed hx rfl : _ ∈ ({x} : Set X))⟩

theorem ncard_cxPts_over_closed : ∀ (Y : Var ℂ) (Z : Set Y.X), (∀ x ∈ Z, IsClosed ({x} : Set Y.X)) → ({y : CxPts Y.str (RingHom.id ℂ) | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z}).ncard = Z.ncard := by
  intro Y Z hZ
  have : LocallyOfFiniteType Y.str := inferInstance
  have him : (fun y : CxPts Y.str (RingHom.id ℂ) => y.1 (closedPoint ℂ)) ''
      {y : CxPts Y.str (RingHom.id ℂ) | y.1 (closedPoint ℂ) ∈ Z} = Z := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := exists_cxPts_pt_eq Y.str (hZ x hx)
      exact ⟨y, hx, rfl⟩
  conv_rhs => rw [← him]
  exact (Set.ncard_image_of_injOn fun _ _ _ _ h => cxPts_eq_of_pt_eq h).symm

end GlobalTheory.CompanionTheory.KoszulCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNegStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_class_twist_neg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s) := by
  first | exact @GlobalTheory.CompanionTheory.ZcDual.dualCl_nu | exact GlobalTheory.CompanionTheory.ZcDual.dualCl_nu | (intros; apply GlobalTheory.CompanionTheory.ZcDual.dualCl_nu <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCliffordLowestVectorStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clifford_lowest_vector : ∀ n : ℕ, ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (c : Fin n → Fin n → Matrix ι ι ℂ),
    IsCliff c ∧ ∃ q : ι → ℂ, q ≠ 0 ∧ ∀ a b, a < b → c b a *ᵥ q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CliffModel.exists_cliff_model | exact GlobalTheory.CompanionTheory.CliffModel.exists_cliff_model | (intros; apply GlobalTheory.CompanionTheory.CliffModel.exists_cliff_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactLieActionStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_lie_action : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)), Continuous ρ → (∀ k v, ‖ρ k v‖ = ‖v‖) → ∃ G : Fin n → Fin n → Module.End ℂ H, Formalism.REAL.GlRel G ∧ (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) ∧ (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.DerivRep.derivative_of_rep | exact GlobalTheory.CompanionTheory.RealCount.DerivRep.derivative_of_rep | (intros; apply GlobalTheory.CompanionTheory.RealCount.DerivRep.derivative_of_rep <;> assumption)
end

