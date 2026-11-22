import Development.AutomorphicArithmetic.PAdicLatticeApproximation.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0017
import Mathlib

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PAdCore
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

open GlobalTheory.AdelicSim

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

private theorem sys_lim {D' : PLat D.O D.inv} (ψ : D'.La ≃+ D.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ} (hw : IsWit D' f nu) :
    ∃ A A' : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), A * A' = 1 ∧ A' * A = 1 ∧ (∀ v ∈ LaHat D, A v ∈ LaHat D) ∧
      (∀ v ∈ LaHat D, A' v ∈ LaHat D) ∧
      ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, A (inAf D x) = inAf D (ψ (f n x)) + n • w := by
  set g : ℕ → D.La →+ D.La := fun n => (ψ : D'.La →+ D.La).comp (f n) with hg
  have hgv : ∀ n x, g n x = ψ (f n x) := fun _ _ => rfl
  have htw : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z := by
    intro n m hn hm hc x
    obtain ⟨e, he⟩ := (hw.1 n m hn hm hc).2 x
    exact ⟨ψ e, by rw [hgv, hgv, he, map_add, map_nsmul]⟩
  have hsurj : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z := by
    intro n hn hc x
    obtain ⟨-, -, -, h4, -⟩ := hw.2 n hn hc
    obtain ⟨a, e, he⟩ := h4 (ψ.symm x)
    refine ⟨a, -ψ e, ?_⟩
    have : x = ψ (f n a) + n • ψ e := by
      rw [← map_nsmul, ← map_add, ← he, AddEquiv.apply_symm_apply]
    rw [hgv, this, smul_neg]; abel
  have hinj : ∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w := by
    intro n hn hc x z h
    obtain ⟨-, -, h3, -, -⟩ := hw.2 n hn hc
    refine (h3 x).1 ⟨ψ.symm z, ?_⟩
    apply ψ.injective
    rw [map_nsmul, AddEquiv.apply_symm_apply, ← hgv, h]
  obtain ⟨g', htw', hgg', hg'g⟩ := invSys D g htw hsurj hinj
  obtain ⟨h₀, h₀L, h₀c⟩ := modLim D g htw
  obtain ⟨h₁, h₁L, h₁c⟩ := modLim D g' htw'
  have inv_of : ∀ (f₀ f₁ : ℕ → D.La →+ D.La) (k₀ k₁ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)),
      (∀ v ∈ LaHat D, k₀ v ∈ LaHat D) →
      (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, k₀ (inAf D x) = inAf D (f₀ n x) + n • w) →
      (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, k₁ (inAf D x) = inAf D (f₁ n x) + n • w) →
      (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, f₀ n (f₁ n x) = x + n • z) → k₀ * k₁ = 1 := by
    intro f₀ f₁ k₀ k₁ hk₀L hk₀ hk₁ hf
    refine ext_inAf D fun x => ?_
    have := modZero D ((k₀ * k₁) (inAf D x) - inAf D x) fun n hn hc => by
      obtain ⟨w, hw, e⟩ := hk₁ n hn hc x
      obtain ⟨w', hw', e'⟩ := hk₀ n hn hc (f₁ n x)
      obtain ⟨z, hz⟩ := hf n hn hc x
      refine ⟨inAf D z + w' + k₀ w, add_mem (add_mem (inAf_mem D z) hw') (hk₀L w hw), ?_⟩
      rw [Module.End.mul_apply, e, map_add, e', hz, inAf_add, inAf_nsmul, map_nsmul]
      simp only [smul_add]; abel
    rw [Module.End.one_apply]; exact sub_eq_zero.1 this
  exact ⟨h₀, h₁, inv_of g g' h₀ h₁ h₀L h₀c h₁c hgg', inv_of g' g h₁ h₀ h₁L h₁c h₀c hg'g, h₀L, h₁L, h₀c⟩

private theorem exists_unit_lim {nu : ℕ → ℤ}
    (ht : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ nu (n * m) - nu n)
    (hc : ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (nu n) (n : ℤ)) :
    ∃ c : (AfP p)ˣ, ∀ n : ℕ, 0 < n → n.Coprime p → ∃ b : AfP p, IsIntAf b ∧ (c : AfP p) = (nu n : AfP p) + n • b := by
  obtain ⟨c, hcI, hcl⟩ := lim p nu ht
  obtain ⟨c', hcc'⟩ := unit p c (fun n => (nu n % n).toNat) fun n hn hnp => by
    obtain ⟨β, hβ, e⟩ := hcl n hn hnp
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnn : 0 ≤ nu n % n := Int.emod_nonneg _ hn'
    have hcast : (((nu n % n).toNat : ℕ) : ℤ) = nu n % n := Int.toNat_of_nonneg hnn
    have h3 := congrArg (Int.cast : ℤ → AfP p) hcast
    rw [Int.cast_natCast] at h3
    have hdiv : nu n = (nu n % n) + n * (nu n / n) := (Int.emod_add_mul_ediv _ _).symm
    refine ⟨?_, (β + ((nu n / n : ℤ) : AfP p)), isInt_add hβ (isInt_intCast _), ?_⟩
    · have hcop := hc n hn hnp
      have h2 : IsCoprime (nu n % n) (n : ℤ) := by
        rw [Int.emod_def]
        simpa [sub_eq_add_neg, mul_comm] using (IsCoprime.add_mul_left_left hcop (-(nu n / n)))
      rw [← hcast] at h2
      exact Nat.isCoprime_iff_coprime.1 h2
    · have e2 : (nu n : AfP p) = (((nu n % n).toNat : ℕ) : AfP p) + (n : AfP p) * ((nu n / n : ℤ) : AfP p) := by
        have h4 := congrArg (Int.cast : ℤ → AfP p) hdiv
        rw [Int.cast_add, Int.cast_mul, ← h3, Int.cast_natCast] at h4
        exact h4
      rw [e, e2, nsmul_eq_mul, nsmul_eq_mul, mul_add]; ring
  exact ⟨⟨c, c', hcc', by rw [mul_comm]; exact hcc'⟩, hcl⟩

private theorem bc_inv (T : VQ D ≃ₗ[ℚ] VQ D) :
    T.toLinearMap.baseChange (AfP p) * T.symm.toLinearMap.baseChange (AfP p) = 1 := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add]

private theorem actOn_inC (L : Link D G) (c : G.C) (u : VQ D) :
    actOn L.rep (AfP p) (inC G (AfP p) c) ((1 : AfP p) ⊗ₜ[ℚ] u) = (1 : AfP p) ⊗ₜ[ℚ] L.rep c u := by
  have h : inC G (AfP p) c = (1 : AfP p) ⊗ₜ[ℚ] c := rfl
  have h2 : ∀ a : AfP p, actOn L.rep (AfP p) (a ⊗ₜ[ℚ] c) = a • (L.rep c).baseChange (AfP p) := by
    intro a
    simp [actOn, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
    rfl
  rw [h, h2]
  simp

private theorem form_one (u w : VQ D) :
    formAf D ((1 : AfP p) ⊗ₜ[ℚ] u) ((1 : AfP p) ⊗ₜ[ℚ] w) = algebraMap ℚ (AfP p) (D.EF.baseChange ℚ u w) := by
  simp [formAf, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]

private theorem cong_iff {A A' : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)} (h : A * A' = 1)
    (hAL : ∀ v ∈ LaHat D, A v ∈ LaHat D) (hA'L : ∀ v ∈ LaHat D, A' v ∈ LaHat D) (z : AfP p ⊗[ℚ] VQ D) :
    A' z ∈ LaHat D ↔ z ∈ LaHat D := by
  refine ⟨fun hz => ?_, hA'L z⟩
  have := hAL _ hz
  rwa [← Module.End.mul_apply, h, Module.End.one_apply] at this

theorem adCore_of : AdCore := by
  intro p _ D G L β D' j hj f nu hw
  obtain ⟨ψ, T, hT⟩ := UpperTheory.exists_rational_equiv_of_isPlace L hj
  obtain ⟨A, A', hAA', hA'A, hAL, hA'L, hAc⟩ := sys_lim ψ hw
  obtain ⟨c, hc⟩ := exists_unit_lim (fun n m a b d => (hw.1 n m a b d).1) (fun n a b => (hw.2 n a b).1)
  obtain ⟨-, hjO, -, s, hs, hsF⟩ := hj
  set Tb := T.toLinearMap.baseChange (AfP p) with hTb
  set Tb' := T.symm.toLinearMap.baseChange (AfP p) with hTb'
  have hTv : ∀ z, Tb ((1 : AfP p) ⊗ₜ[ℚ] z) = (1 : AfP p) ⊗ₜ[ℚ] T z := fun z => by simp [hTb]
  have hTv' : ∀ z, Tb' ((1 : AfP p) ⊗ₜ[ℚ] z) = (1 : AfP p) ⊗ₜ[ℚ] T.symm z := fun z => by simp [hTb']
  have hTT' : Tb * Tb' = 1 := bc_inv T
  have hT'T : Tb' * Tb = 1 := by simpa using bc_inv T.symm
  have gg' : (Tb * A) * (A' * Tb') = 1 := by
    rw [_root_.mul_assoc, ← _root_.mul_assoc A, hAA', _root_.one_mul, hTT']
  have g'g : (A' * Tb') * (Tb * A) = 1 := by
    rw [_root_.mul_assoc, ← _root_.mul_assoc Tb', hT'T, _root_.one_mul, hA'A]
  have c0 : ∀ b : D.O, (Tb * A) * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * (Tb * A) :=
    UpperTheory.primeToP_isogeny_of_adelic_endo_preserving_lattice ψ T hT hjO (fun n a b => (hw.2 n a b).2.1) A hAL hAc
  have c1 : ∀ b : D.O, (A' * Tb') * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * (A' * Tb') := by
    intro b
    calc (A' * Tb') * (actQ D b).baseChange (AfP p)
        = (A' * Tb') * ((actQ D b).baseChange (AfP p) * ((Tb * A) * (A' * Tb'))) := by rw [gg', _root_.mul_one]
      _ = (A' * Tb') * ((Tb * A) * (actQ D b).baseChange (AfP p)) * (A' * Tb') := by
          rw [c0 b]; simp only [_root_.mul_assoc]
      _ = _ := by rw [← _root_.mul_assoc (A' * Tb'), g'g, _root_.one_mul]
  obtain ⟨y, hy⟩ := comm L (Tb * A) c0
  obtain ⟨y', hy'⟩ := comm L (A' * Tb') c1
  have yy' : y * y' = 1 := inj L (by rw [map_mul, hy, hy', gg', map_one])
  have y'y : y' * y = 1 := inj L (by rw [map_mul, hy, hy', g'g, map_one])
  have hform : ∀ v w, algebraMap ℚ (AfP p) s * formAf D (actOn L.rep (AfP p) (inC G (AfP p) ((β⁻¹ : G.Cˣ) : G.C))
      (actOn L.rep (AfP p) y v)) (actOn L.rep (AfP p) y w) = (2 * (c : AfP p)) * formAf D v w := by
    set B := actOn L.rep (AfP p) (inC G (AfP p) ((β⁻¹ : G.Cˣ) : G.C)) with hB
    set F : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D) :=
      algebraMap ℚ (AfP p) s • (formAf D).compl₁₂ (B * Tb) Tb with hFdef
    have hFv : ∀ v w, F v w = algebraMap ℚ (AfP p) s * formAf D (B (Tb v)) (Tb w) := fun v w => by
      simp only [hFdef, LinearMap.smul_apply, LinearMap.compl₁₂_apply, Module.End.mul_apply, Algebra.smul_def]
      rfl
    have key := UpperTheory.form_scalar_of_adelic_endo_preserving_lattice F (fun x x' => D'.EF (ψ.symm x) (ψ.symm x')) (fun x x' => by
        have h1 : ∀ x, Tb (inAf D x) = (1 : AfP p) ⊗ₜ[ℚ] j (ψ.symm x) := fun x => by
          rw [inAf, hTv, ← hT, ψ.apply_symm_apply]
        rw [hFv, h1, h1, hB, actOn_inC, form_one]
        show _ = ((D'.EF (ψ.symm x) (ψ.symm x') : ℤ) : AfP p)
        have h2 := hsF (ψ.symm x) (ψ.symm x')
        rw [← map_mul]
        have h3 : s * (D.EF.baseChange ℚ) (L.rep ((β⁻¹ : G.Cˣ) : G.C) (j (ψ.symm x))) (j (ψ.symm x')) =
            ((D'.EF (ψ.symm x) (ψ.symm x') : ℤ) : ℚ) := h2.symm
        rw [h3, map_intCast])
      A hAL (fun n => (ψ : D'.La →+ D.La).comp (f n)) hAc nu c hc (fun n hn hnp x x' => by
        obtain ⟨-, -, -, -, h5⟩ := hw.2 n hn hnp
        simpa using h5 x x')
    intro v w
    have h1 := key v w
    rw [hFv] at h1
    rw [hy]
    exact h1
  obtain ⟨t, ht⟩ := UpperTheory.exists_unit_triv_of_similitude_factor L β y y' y'y yy' s hs c hform
  have hrd : ∀ w, rd L ⟨y', y, y'y, yy'⟩ 1 w = A' ((1 : AfP p) ⊗ₜ[ℚ] T.symm w) := by
    intro w
    simp only [rd, inv_one, map_one, Module.End.one_apply, hy']
    rw [Module.End.mul_apply, hTv']
  refine ⟨⟨y', y, y'y, yy'⟩, t, ht, fun n hn hnp => ⟨fun w => ?_, fun a => ?_⟩⟩
  · rw [hrd, cong_iff hAA' hAL hA'L, UpperTheory.one_tmul_mem_completedLattice_iff]
    constructor
    · rintro ⟨r, u, h⟩
      refine ⟨r, ψ u, ?_⟩
      apply T.injective
      rw [map_nsmul, T.apply_symm_apply, h, hT]
    · rintro ⟨r, x, h⟩
      refine ⟨r, ψ.symm x, ?_⟩
      rw [← hT, ψ.apply_symm_apply, ← h, map_nsmul, T.apply_symm_apply]
  · obtain ⟨w, hwL, e⟩ := hAc n hn hnp a
    refine ⟨-(A' w), neg_mem (hA'L w hwL), ?_⟩
    have h1 : T.symm (j (f n a)) = (1 : ℚ) ⊗ₜ[ℤ] ψ (f n a) := by rw [← hT, T.symm_apply_apply]
    have h2 : (1 : AfP p) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] ψ (f n a)) = A (inAf D a) - n • w := by
      rw [e, add_sub_cancel_right]; rfl
    rw [hrd, h1, h2, map_sub, map_nsmul, ← Module.End.mul_apply, hA'A, Module.End.one_apply, smul_neg, sub_eq_add_neg]

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem trace_conj {F : Type} [Field F] [NumberField F] [IsCMField F] (x : F) :
    Algebra.trace ℚ F (IsCMField.complexConj F x) = Algebra.trace ℚ F x := by
  let e : F ≃ₐ[ℚ] F := AlgEquiv.ofRingEquiv (f := (IsCMField.complexConj F).toRingEquiv) (fun r => by simp)
  exact Algebra.trace_eq_of_algEquiv e x

private theorem trace_strip {F : Type} [Field F] [NumberField F] {a b : F}
    (h : ∀ x : F, Algebra.trace ℚ F (a * x) = Algebra.trace ℚ F (b * x)) : a = b := by
  have hnd := traceForm_nondegenerate ℚ F
  have : a - b = 0 := by
    apply hnd.1
    intro x
    show Algebra.trace ℚ F ((a - b) * x) = 0
    rw [sub_mul, map_sub, h, sub_self]
  exact sub_eq_zero.1 this

private theorem exists_trace_rep {F : Type} [Field F] [NumberField F] (f : F →+ ℚ) :
    ∃ a : F, ∀ x, Algebra.trace ℚ F (a * x) = f x := by
  have hnd := traceForm_nondegenerate ℚ F
  refine ⟨(LinearMap.BilinForm.toDual _ hnd).symm f.toRatLinearMap, fun x => ?_⟩
  exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) f.toRatLinearMap x

private theorem sum_single {F : Type} [Field F] {n : ℕ} (u : Fin n → F) :
    u = ∑ j, u j • (Pi.single j 1 : Fin n → F) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

private theorem form_ext {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ}
    {M N : Matrix (Fin n) (Fin n) F}
    (h : ∀ u w : Fin n → F, Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (M *ᵥ u)) =
      Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (N *ᵥ u))) : M = N := by
  ext i j
  apply trace_strip
  intro x
  have := h (x • Pi.single j 1) (Pi.single i 1)
  have e : ∀ P : Matrix (Fin n) (Fin n) F,
      (fun k => IsCMField.complexConj F ((Pi.single i 1 : Fin n → F) k)) ⬝ᵥ (P *ᵥ (x • Pi.single j 1)) = P i j * x := by
    intro P
    have e1 : (fun k => IsCMField.complexConj F ((Pi.single i 1 : Fin n → F) k)) = (Pi.single i 1 : Fin n → F) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [e1, Matrix.mulVec_smul, Matrix.mulVec_single_one, single_one_dotProduct]
    simp [mul_comm]
  rwa [e M, e N] at this

private theorem form_core {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ}
    (B : (Fin n → F) →+ (Fin n → F) →+ ℚ)
    (hadj : ∀ (x : F) u w, B (x • u) w = B u (IsCMField.complexConj F x • w))
    (hskew : ∀ u w, B u w = - B w u)
    (hnd : ∀ u, (∀ w, B u w = 0) → u = 0) :
    ∃ A : Matrix (Fin n) (Fin n) F, A.det ≠ 0 ∧ (A.map (IsCMField.complexConj F))ᵀ = -A ∧
      ∀ u w, B u w = Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (A *ᵥ u)) := by
  have hrep : ∀ i j : Fin n, ∃ a : F, ∀ x, Algebra.trace ℚ F (a * x) =
      B (x • (Pi.single j 1 : Fin n → F)) (Pi.single i 1) := fun i j =>
    exists_trace_rep (((AddMonoidHom.eval (Pi.single i 1 : Fin n → F)).comp B).comp
      (AddMonoidHom.mk' (fun x : F => x • (Pi.single j 1 : Fin n → F)) (fun a b => add_smul a b _)))
  choose A₀ hA₀ using hrep
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) F, ∀ i j x, Algebra.trace ℚ F (A i j * x) =
      B (x • (Pi.single j 1 : Fin n → F)) (Pi.single i 1) := ⟨A₀, hA₀⟩
  have hterm : ∀ (u w : Fin n → F) i j, B (u j • (Pi.single j 1 : Fin n → F)) (w i • (Pi.single i 1 : Fin n → F)) =
      Algebra.trace ℚ F (IsCMField.complexConj F (w i) * (A i j * u j)) := by
    intro u w i j
    have e1 : B (u j • (Pi.single j 1 : Fin n → F)) (w i • (Pi.single i 1 : Fin n → F)) =
        B (IsCMField.complexConj F (w i) • (u j • (Pi.single j 1 : Fin n → F))) (Pi.single i 1) := by
      rw [hadj (IsCMField.complexConj F (w i)) (u j • _), IsCMField.complexConj_apply_apply]
    rw [e1, smul_smul, ← hA]
    congr 1
    ring
  have hform : ∀ u w, B u w = Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (A *ᵥ u)) := by
    intro u w
    conv_lhs => rw [sum_single u, sum_single w]
    simp only [map_sum, AddMonoidHom.finset_sum_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, hterm]
  refine ⟨A, ?_, ?_, hform⟩
  · intro hdet
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    exact hv (hnd v fun w => by rw [hform, hAv]; simp)
  · ext i j
    show IsCMField.complexConj F (A j i) = - A i j
    apply trace_strip
    intro x
    have h1 : Algebra.trace ℚ F (IsCMField.complexConj F (A j i) * x) =
        Algebra.trace ℚ F (A j i * IsCMField.complexConj F x) := by
      rw [← trace_conj (A j i * IsCMField.complexConj F x), map_mul (IsCMField.complexConj F), IsCMField.complexConj_apply_apply]
    rw [h1, hA, hadj, IsCMField.complexConj_apply_apply, hskew, ← hA, neg_mul, map_neg]

private theorem bc_skew {La : Type} [AddCommGroup La] (E : LinearMap.BilinForm ℤ La) (halt : ∀ x, E x x = 0)
    (u w : ℚ ⊗[ℤ] La) : E.baseChange ℚ u w = - E.baseChange ℚ w u := by
  have hs : ∀ x y, E x y = - E y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, neg_add]
  | tmul a x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [map_add, LinearMap.add_apply, hc, hd, neg_add]
    | tmul b y =>
      simp only [LinearMap.BilinForm.baseChange_tmul]
      rw [hs x y]
      simp [mul_comm]

private theorem exists_pure {La : Type} [AddCommGroup La] (v : ℚ ⊗[ℤ] La) :
    ∃ (N : ℕ) (x : La), N ≠ 0 ∧ N • v = (1 : ℚ) ⊗ₜ[ℤ] x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | add a b ha hb =>
    obtain ⟨N, x, hN, hx⟩ := ha
    obtain ⟨M, y, hM, hy⟩ := hb
    refine ⟨N * M, M • x + N • y, mul_ne_zero hN hM, ?_⟩
    rw [smul_add, TensorProduct.tmul_add, mul_comm N M, mul_smul, hx, mul_comm M N, mul_smul, hy,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  | tmul a x =>
    refine ⟨a.den, a.num • x, a.den_ne_zero, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    congr 1
    rw [nsmul_eq_mul, zsmul_eq_mul, _root_.mul_one, Rat.den_mul_eq_num]

private theorem bc_nondeg {La : Type} [AddCommGroup La] (E : LinearMap.BilinForm ℤ La)
    (hE : Function.Injective E) (v : ℚ ⊗[ℤ] La) (h : ∀ w, E.baseChange ℚ v w = 0) : v = 0 := by
  obtain ⟨N, x, hN, hx⟩ := exists_pure v
  have hx0 : x = 0 := by
    apply hE
    ext y
    have h1 := h ((1 : ℚ) ⊗ₜ[ℤ] y)
    have h2 : E.baseChange ℚ (N • v) ((1 : ℚ) ⊗ₜ[ℤ] y) = 0 := by simp [h1]
    rw [hx, LinearMap.BilinForm.baseChange_tmul] at h2
    simpa using h2
  rw [hx0, TensorProduct.tmul_zero] at hx
  have : (N : ℚ) • v = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hx
  exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hN)

theorem UpperTheory.Gal.W2.fForm_of :
    UpperTheory.Gal.W2.FForm := by
  intro p _ D G L kp σ hF
  let E := D.EF.baseChange ℚ
  let B : (Fin G.n → G.F) →+ (Fin G.n → G.F) →+ ℚ :=
    AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun w => E (kp.symm u) (kp.symm w)) (by intro a b; simp))
      (by intro a b; ext w; simp)
  have hB : ∀ u w, B u w = E (kp.symm u) (kp.symm w) := fun _ _ => rfl
  have hsc : ∀ (x : G.F) (u : Fin G.n → G.F),
      kp.symm (x • u) = L.rep (algebraMap G.F G.C x) (kp.symm u) := by
    intro x u
    apply kp.injective
    rw [AddEquiv.apply_symm_apply, hF, AddEquiv.apply_symm_apply, AlgEquiv.commutes]
    ext i
    simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]
  have hsm : ∀ (c : G.C) (u : Fin G.n → G.F), kp.symm (σ c *ᵥ u) = L.rep c (kp.symm u) := by
    intro c u
    apply kp.injective
    rw [AddEquiv.apply_symm_apply, hF, AddEquiv.apply_symm_apply]
  obtain ⟨A, hdet, hskew, hform⟩ := form_core B
    (by
      intro x u w
      rw [hB, hB, hsc, hsc, L.adj]
      show E _ (L.rep ((G.star _).unop) _) = _
      rw [G.star_F])
    (by intro u w; exact bc_skew D.EF D.alt _ _)
    (by
      intro u hu
      have h0 : kp.symm u = 0 := bc_nondeg D.EF D.nondeg _ fun w => by
        have := hu (kp w)
        rwa [hB, AddEquiv.symm_apply_apply] at this
      simpa using congrArg kp h0)
  have hform' : ∀ u w, E u w = Algebra.trace ℚ G.F ((fun i => IsCMField.complexConj G.F (kp w i)) ⬝ᵥ (A *ᵥ kp u)) := by
    intro u w
    have := hform (kp u) (kp w)
    rwa [hB, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply] at this
  refine ⟨A, hdet, hskew, hform', fun c => ?_⟩
  apply form_ext
  intro u w
  have hcj : (fun i => IsCMField.complexConj G.F (w i)) ⬝ᵥ
        (((σ c).map (IsCMField.complexConj G.F))ᵀ * A) *ᵥ u =
      (fun i => IsCMField.complexConj G.F ((σ c *ᵥ w) i)) ⬝ᵥ (A *ᵥ u) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    congr 1
    ext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [hcj, ← Matrix.mulVec_mulVec]
  have h1 := hform (σ (sh G c) *ᵥ u) w
  have h2 := hform u (σ c *ᵥ w)
  rw [← h1, ← h2, hB, hB, hsm, hsm]
  have h3 : sh G (sh G c) = c := G.star_star c
  have h4 := L.adj (sh G c) (kp.symm u) (kp.symm w)
  rw [h3] at h4
  exact h4
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFixGa
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem isCoordA_of_dvd {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {G : HTGroup p} (L : Link D G)
    {x : (AfP p ⊗[ℚ] G.C)ˣ} {N N' : ℕ} (hd : N ∣ N') {D' : PLat D.O D.inv} {t : D.La → D'.La}
    {j : D'.La →+ VQ D} {h₁ : G.GAf} (h : IsCoordA L x N' D' t j h₁) : IsCoordA L x N D' t j h₁ := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun a => ?_⟩
  obtain ⟨w, hw, e⟩ := h2 a
  exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩

theorem UpperTheory.Gal.W2.fixGa_of :
    UpperTheory.Gal.W2.HeckeCoord → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.FixLine → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.IntMult → UpperTheory.Gal.W2.FixGa := by
  intro hHC hLI hFL hAY hIM p _ D G L gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine v t₀ B PD RD D' t hcls P j a hco x e hU y hsee
  obtain ⟨hpl, hca, hloc, Q₀, hQ₀, hQ₀j, hrel⟩ := hco
  obtain ⟨h3, hcp, h3', hcp', hd, hconj⟩ := hlev
  obtain ⟨D'', t'', P'', e'', inc, j'', hcls'', hU'', hP, he, hinc, hj, hpl'', hco'', hloc''⟩ :=
    hHC p D G L gb N N' h ⟨h3, hcp, h3', hcp', hd, hconj⟩ X X' c₂ hX hL hX' hL' ρ hfine D' t P x e hU B j a.1.1
      (PD.lat a.1.2) hpl hca hloc
  obtain ⟨hfix, hS, hK⟩ := hsee
  have hN : 0 < N := by omega
  have hS' : h * (a.1.1⁻¹ * B.toAf y * a.1.1) ∈ L.KN N := hS
  obtain ⟨w, hw, hwj⟩ := (hLI p D G L B PD N hN hcp D' t D'' t'' j j'' a.1 (a.1.1 * h⁻¹, a.1.2) N' N t t''
    hcls hcls'' hpl hpl'' (isCoordA_of_dvd L hd hca) hco'' hloc hloc'' y⁻¹).1 (by
      constructor
      · have := (L.KN N).inv_mem hS'
        simp only [map_inv, _root_.mul_inv_rev, _root_.inv_inv, _root_.mul_assoc] at this ⊢
        exact this
      · have := (KHT p G.m G.n 1 G.Fw).inv_mem hK
        simp only [map_inv, _root_.mul_inv_rev, _root_.inv_inv, _root_.mul_assoc] at this ⊢
        exact this)
  have hfix' := (hFL p D G L v t₀ ρ B.β RD Q₀ a.2 hQ₀ hrel y).2 hfix
  obtain ⟨H, hH⟩ := (hFL p D G L v t₀ ρ B.β RD Q₀ a.2 hQ₀ hrel y⁻¹).1.1 hfix'
  have hga : ∀ u, j (w (inc u)) = actY L y⁻¹ (j u) := fun u => by rw [hwj, hj]
  have hQQ : ∀ Q : VQ D →+ Fin D.g → ℂ, (∀ u, Q (j u) = P u) → ∀ w₀, Q w₀ = Q₀ w₀ := by
    intro Q hQj w₀
    obtain ⟨m, u, hm, hmu⟩ := hpl.2.2.1 w₀
    apply smul_right_injective (Fin D.g → ℂ) hm
    simp only
    rw [← map_nsmul Q, ← map_nsmul Q₀, hmu, hQj, hQ₀j]
  obtain ⟨s, hs, hEF⟩ := hpl.2.2.2
  have hpos : (0 : ℚ) < ((y⁻¹ : LKCx.grp G B.β) : G.Cˣ × ℚˣ).2 := (y⁻¹).2.2
  have hmul : ∀ u u' : D'.La, (((D'.EF ((w.toLinearMap ∘ₗ inc) u)) ((w.toLinearMap ∘ₗ inc) u') : ℤ) : ℚ) =
      (((y⁻¹ : LKCx.grp G B.β) : G.Cˣ × ℚˣ).2 : ℚ) * ((D'.EF u u' : ℤ) : ℚ) := by
    intro u u'
    show (((D'.EF (w (inc u))) (w (inc u')) : ℤ) : ℚ) = _
    rw [hEF, hEF, hga, hga, (hAY p D G L B.β y⁻¹).1]
    ring
  obtain ⟨m, hm, hm'⟩ := hIM D.O D.inv D' (w.toLinearMap ∘ₗ inc) _ hpos hmul
  refine ⟨w.toLinearMap ∘ₗ inc, H, fun u => hga u, ⟨⟨m, hm, hm'⟩, fun u => ?_⟩, fun w' Q hQj hQ => ?_⟩
  · show P (w (inc u)) = H *ᵥ P u
    rw [← hQ₀j, ← hQ₀j, hga, hH]
  · rw [hQQ Q hQj, hQQ Q hQj, hH]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrame
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

abbrev Loc (G : HTGroup p) : Type := (w : Fin G.m) → Fin G.n → G.Fw w

def IntL (z : Loc G) : Prop := ∀ w i, ‖(z w i : PadicAlgCl p)‖ ≤ 1

def pairL (a b : Loc G) : ℚ_[p] := ∑ w, Algebra.trace ℚ_[p] (G.Fw w) (a w ⬝ᵥ b w)

structure PFrame (β : G.Cˣ) where
  T : VQ D →+ Loc G
  T' : VQ D →+ Loc G
  act : ∀ (c : G.C) x w, T (L.rep c x) w = G.rho w c *ᵥ T x w
  act' : ∀ (c : G.C) x w, T' (L.rep c x) w = (G.rho w ((β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C)))ᵀ *ᵥ T' x w
  form : ∀ u x, ((formB L β u x : ℚ) : ℚ_[p]) = pairL (T' x) (T u) - pairL (T' u) (T x)
  dense : ∀ (a b : Loc G) (k : ℕ), ∃ x a' b', IntL a' ∧ IntL b' ∧ T x = a + p ^ k • a' ∧ T' x = b + p ^ k • b'
  bound : ∃ (s : Finset (VQ D)) (k : ℕ), Submodule.span ℚ (s : Set (VQ D)) = ⊤ ∧
    ∀ x, IntL (T x) → IntL (T' x) → ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set (VQ D))

variable {L}

def PFrame.Mem {β : G.Cˣ} (A : PFrame L β) (g : Gp G) (x : VQ D) : Prop :=
  IntL (fun w => (((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ A.T x w) ∧
    ∀ z : Loc G, IntL z → ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * pairL (A.T' x) (fun w => (g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w)‖ ≤ 1

def IntPt (g : Gp G) : Prop :=
  ‖(g.1 : ℚ_[p])‖ = 1 ∧ ∀ w i j, ‖((g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : PadicAlgCl p)‖ ≤ 1 ∧
    ‖((((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : PadicAlgCl p)‖ ≤ 1

end UpperTheory.Gal.W2
end
end

