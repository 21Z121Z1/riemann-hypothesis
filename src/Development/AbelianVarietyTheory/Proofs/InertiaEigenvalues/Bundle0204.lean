import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0192
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0195
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0151
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0197
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0171
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0125
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0168
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0184
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0142
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0196

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConnectionSemisimpleEigenvalues
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.LcSemisimple

theorem chain_aeval_mem : ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (F : ℤ → Submodule K V) (lam : ℤ → K) (W W' : Submodule K V) (a b : ℤ) (J : Finset ℤ), a ≤ b → (∀ j, ∀ x ∈ F j, T x - lam j • x ∈ F (j + 1)) → (∀ x ∈ W, T x ∈ W) → (∀ x ∈ W', T x ∈ W') → W ≤ W' → F b ≤ W → W' ≤ F a → (∀ j, a ≤ j → j < b → j ∉ J → W' ⊓ F j ≤ W ⊓ F j ⊔ F (j + 1)) → ∀ x ∈ W', Polynomial.aeval T (∏ j ∈ J, (Polynomial.X - Polynomial.C (lam j))) x ∈ W := by
  intro K V _ _ _ T F lam W W' a b J hab hstep hW hW' hWW' hb ha hJ
  classical
  have hWq : ∀ (q : Polynomial K), ∀ w ∈ W, Polynomial.aeval T q w ∈ W := by
    intro q
    refine Polynomial.induction_on q (fun c w hw => ?_) (fun p q hp hq w hw => ?_)
      (fun n c ih w hw => ?_)
    · simpa [Algebra.algebraMap_eq_smul_one] using W.smul_mem c hw
    · simpa using W.add_mem (hp w hw) (hq w hw)
    · have e1 : Polynomial.aeval T (Polynomial.C c * Polynomial.X ^ (n + 1)) w =
          Polynomial.aeval T (Polynomial.C c * Polynomial.X ^ n) (T w) := by
        rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
      rw [e1]
      exact ih _ (hW w hw)
  have key : ∀ n : ℕ, (n : ℤ) ≤ b - a → ∀ J' : Finset ℤ,
      (∀ j ∈ J, b - n ≤ j → j < b → j ∈ J') → ∀ x ∈ W' ⊓ F (b - n),
      Polynomial.aeval T (∏ j ∈ J', (Polynomial.X - Polynomial.C (lam j))) x ∈ W := by
    intro n
    induction n with
    | zero =>
      intro _ J' _ x hx
      exact hWq _ x (hb (by simpa using (Submodule.mem_inf.1 hx).2))
    | succ n ih =>
      intro hn J' hJ' x hx
      obtain ⟨k, hk⟩ : ∃ k, k = b - ((n + 1 : ℕ) : ℤ) := ⟨_, rfl⟩
      rw [← hk] at hx
      have hk' : k = b - n - 1 := by rw [hk]; push_cast; ring
      have hk1 : k + 1 = b - n := by omega
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
      by_cases hkJ : k ∈ J'
      · rw [← Finset.prod_erase_mul J' _ hkJ, map_mul, Module.End.mul_apply]
        have hy : T x - lam k • x ∈ W' ⊓ F (b - n) :=
          Submodule.mem_inf.2 ⟨W'.sub_mem (hW' x hx1) (W'.smul_mem _ hx1), hk1 ▸ hstep k x hx2⟩
        have h2 : Polynomial.aeval T (Polynomial.X - Polynomial.C (lam k)) x = T x - lam k • x := by
          simp [Algebra.algebraMap_eq_smul_one]
        rw [h2]
        refine ih (by omega) (J'.erase k) (fun j hj h1 h3 => Finset.mem_erase.2 ⟨by omega,
          hJ' j hj (by push_cast; omega) h3⟩) _ hy
      · have hkJ0 : k ∉ J := fun h => hkJ (hJ' k h (by push_cast; omega) (by omega))
        have h1 := hJ k (by push_cast at hn; omega) (by omega) hkJ0 (Submodule.mem_inf.2 ⟨hx1, hx2⟩)
        obtain ⟨w, hw, f, hf, rfl⟩ := Submodule.mem_sup.1 h1
        rw [map_add]
        have hf' : f ∈ W' ⊓ F (b - n) := by
          refine Submodule.mem_inf.2 ⟨?_, hk1 ▸ hf⟩
          simpa using W'.sub_mem hx1 (hWW' (Submodule.mem_inf.1 hw).1)
        exact W.add_mem (hWq _ w (Submodule.mem_inf.1 hw).1)
          (ih (by omega) J' (fun j hj h3 h4 => hJ' j hj (by push_cast; omega) h4) f hf')
  intro x hx
  refine key (b - a).toNat (by omega) J (fun j hj _ _ => hj) x (Submodule.mem_inf.2 ⟨hx, ?_⟩)
  rw [show b - ((b - a).toNat : ℤ) = a by omega]
  exact ha hx

theorem aeval_intertwine {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (g : V →ₗ[K] V') (f : Module.End K V) (f' : Module.End K V')
    (h : ∀ x, g (f x) = f' (g x)) (q : Polynomial K) (x : V) : g (Polynomial.aeval f q x) = Polynomial.aeval f' q (g x) := by
  suffices H : ∀ x, g (Polynomial.aeval f q x) = Polynomial.aeval f' q (g x) from H x
  refine Polynomial.induction_on q (fun c x => ?_) (fun p q hp hq x => ?_) (fun n c ih x => ?_)
  · simp [Algebra.algebraMap_eq_smul_one]
  · simp [hp, hq]
  · have e1 : Polynomial.aeval f (Polynomial.C c * Polynomial.X ^ (n + 1)) x = Polynomial.aeval f (Polynomial.C c * Polynomial.X ^ n) (f x) := by
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    have e2 : Polynomial.aeval f' (Polynomial.C c * Polynomial.X ^ (n + 1)) (g x) = Polynomial.aeval f' (Polynomial.C c * Polynomial.X ^ n) (f' (g x)) := by
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    rw [e1, e2, ih, h]

theorem ker_aeval_prod {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (v : ℤ → K) (hv : Function.Injective v) (s : Finset ℤ) :
    LinearMap.ker (Polynomial.aeval f (∏ i ∈ s, (Polynomial.X - Polynomial.C (v i)))) = ⨆ i ∈ s, f.eigenspace (v i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
    exact LinearMap.ker_id
  · intro a s ha ih
    rw [Finset.prod_insert ha, ← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime, ih, Finset.iSup_insert]
    · congr 1
      rw [Module.End.eigenspace_def, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    · exact IsCoprime.prod_right fun i hi =>
        (Polynomial.pairwise_coprime_X_sub_C hv) (fun h => ha (h ▸ hi))

theorem semisimple_of_aeval {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (s : Finset ℤ) (v : ℤ → K) (hv : Function.Injective v)
    (h : Polynomial.aeval f (∏ n ∈ s, (Polynomial.X - Polynomial.C (v n))) = 0) :
    f.IsSemisimple ∧ (∀ μ, f.HasEigenvalue μ → ∃ n ∈ s, μ = v n) ∧
      ⨆ n ∈ s, f.eigenspace (v n) = ⊤ := by
  refine ⟨Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    ((Polynomial.separable_prod_X_sub_C_iff'.2 hv.injOn).squarefree) h, fun μ hμ => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := ∏ n ∈ s, (Polynomial.X - Polynomial.C (v n))) hx
    rw [h, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h1
      obtain ⟨n, hn, h2⟩ := h1
      exact ⟨n, hn, by simpa [sub_eq_zero] using h2⟩
    · exact absurd h1 hx.2
  · rw [← ker_aeval_prod f v hv s, h, LinearMap.ker_zero]

theorem lc_semisimple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ U : Finset ℤ, D.jumps ⊆ U → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Semisimple D U := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D U hU
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne e)
  set Lan := D.ext (Rpi O K l e) with hLan
  let F : ℤ → Submodule K (Vec K a ι) := fun j => (shiftE l e j Lan).restrictScalars K
  let lam : ℤ → K := fun j => ((-j * e * l : ℤ) : K)
  let J : Finset ℤ := (GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.shifts U η).image (fun n => -n)
  have hp : ∏ j ∈ J, (Polynomial.X - Polynomial.C (lam j)) =
      ∏ n ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.shifts U η, (Polynomial.X - Polynomial.C (((n * e * l : ℤ) : K))) := by
    rw [Finset.prod_image (fun x _ y _ h => neg_injective h)]
    simp [lam]
  have hstep : ∀ j, ∀ x ∈ F j, D.EN x - lam j • x ∈ F (j + 1) := by
    intro j x hx
    have h1 := GlobalTheory.T.eulerE_add_smul_mem_eisenstein_shift_graded O K l e a ι η H D j x hx
    have h2 : D.EN x - lam j • x = D.EN x + ((j * e * l : ℤ) : K) • x := by
      rw [sub_eq_add_neg, ← neg_smul]
      congr 2
      simp only [lam]
      push_cast
      ring
    rw [h2]
    exact h1
  have hb : F η ≤ D.Man := by
    intro x hx
    have h1 := D.smul_mem_Mext (A_le_Rpi l e) ((mem_shiftE).1 hx)
    rwa [smul_smul, E_pow_mul_Ezpow_neg, one_smul] at h1
  have ha : divE l e η D.Man ≤ F (-((η : ℤ) + H)) := by
    intro x hx
    have h1 := D.smul_mem_ext_of_basis (c := E K l e ^ H) (fun i => D.lower _ (D.bas_mem_M i))
      (A_le_Rpi l e) ((mem_divE).1 hx)
    show Ezpow K l e (-(-((η : ℤ) + H))) • x ∈ Lan
    rwa [neg_neg, Ezpow_add, Ezpow_natCast, Ezpow_natCast, mul_comm, mul_smul]
  have hJ : ∀ j, -((η : ℤ) + H) ≤ j → j < η → j ∉ J →
      divE l e η D.Man ⊓ F j ≤ D.Man ⊓ F j ⊔ F (j + 1) := by
    intro j _ _ hj x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hx1' : E K l e ^ η • x ∈ D.Man := hx1
    have hx2' : Ezpow K l e (-j) • x ∈ Lan := hx2
    have hnj : ∀ i, -j - η ≤ i → i ≤ -j - 1 → D.filL (i + 1) = D.filL i := by
      intro i h1 h2
      by_contra hne
      have hi : i ∈ U := hU (show i ∈ D.jumps from hne)
      exact hj (Finset.mem_image.2 ⟨-j, GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.mem_shifts.2
        ⟨i, hi, -j - i, ⟨by omega, by omega⟩, by ring⟩, neg_neg j⟩)
    have hFA : ∀ i, D.filL (i + 1) = D.filL i → ∀ y,
        y ∈ (Lan ⊓ shiftE l e i (D.Mext (Rpi O K l e))) ⊔ shiftE l e 1 Lan →
        y ∈ (Lan ⊓ shiftE l e (i + 1) (D.Mext (Rpi O K l e))) ⊔ shiftE l e 1 Lan := by
      intro i h y hy
      rw [GlobalTheory.T.mem_analytic_filtration_iff_lattice_filtration_add O K l e a ι D.toPhiMod i y] at hy
      rw [GlobalTheory.T.mem_analytic_filtration_iff_lattice_filtration_add O K l e a ι D.toPhiMod (i + 1) y, h]
      exact hy
    have hchain : ∀ k : ℕ, k ≤ η → ∀ y,
        y ∈ (Lan ⊓ shiftE l e (-j - η) (D.Mext (Rpi O K l e))) ⊔ shiftE l e 1 Lan →
        y ∈ (Lan ⊓ shiftE l e (-j - η + k) (D.Mext (Rpi O K l e))) ⊔ shiftE l e 1 Lan := by
      intro k
      induction k with
      | zero => intro _ y hy; simpa using hy
      | succ k ih =>
        intro hk y hy
        have h1 := hFA (-j - η + k) (hnj _ (by omega) (by omega)) y (ih (by omega) y hy)
        rwa [show -j - (η : ℤ) + k + 1 = -j - η + ((k + 1 : ℕ) : ℤ) by push_cast; ring] at h1
    set z := Ezpow K l e (-j) • x with hz
    have hz1 : z ∈ (Lan ⊓ shiftE l e (-j - η) (D.Mext (Rpi O K l e))) ⊔ shiftE l e 1 Lan := by
      refine Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hx2', ?_⟩)
      rw [mem_shiftE, hz, smul_smul, ← Ezpow_add, show -(-j - (η : ℤ)) + -j = η by ring,
        Ezpow_natCast]
      exact hx1'
    have hz2 := hchain η le_rfl z hz1
    rw [show -j - (η : ℤ) + η = -j by ring] at hz2
    obtain ⟨w, hw, f, hf, hwf⟩ := Submodule.mem_sup.1 hz2
    obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hw
    have hxz : x = Ezpow K l e j • w + Ezpow K l e j • f := by
      rw [← smul_add, hwf, hz, smul_smul, ← Ezpow_add, add_neg_cancel]
      simp [Ezpow]
    rw [hxz]
    refine Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨?_, ?_⟩) ?_
    · have h1 : Ezpow K l e (-(-j)) • w ∈ D.Mext (Rpi O K l e) := (mem_shiftE).1 hw2
      rwa [neg_neg] at h1
    · show Ezpow K l e (-j) • Ezpow K l e j • w ∈ Lan
      rwa [smul_smul, Ezpow_neg_mul, one_smul]
    · show Ezpow K l e (-(j + 1)) • Ezpow K l e j • f ∈ Lan
      rw [smul_smul, ← Ezpow_add, show -(j + 1) + j = -1 by ring]
      exact (mem_shiftE).1 hf
  have key := chain_aeval_mem D.EN F lam D.Man (divE l e η D.Man) (-((η : ℤ) + H)) η J (by omega) hstep
    (fun x hx => D.EN_mem_Man hx) (fun x hx => D.EN_mem_divE hx)
    (fun x hx => (mem_divE).2 (D.smul_mem_Man (pow_mem (E_mem l e _) η) hx)) hb ha hJ
  rw [hp] at key
  have hann : ∀ w ∈ D.PolEta η, Polynomial.aeval D.Lc
      (∏ n ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.shifts U η, (Polynomial.X - Polynomial.C (((n * e * l : ℤ) : K)))) w = 0 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← aeval_intertwine D.cls D.EN D.Lc (fun _ => rfl)]
    exact (D.cls_eq_zero_iff).2 (key y hy)
  have hZ : Polynomial.aeval D.LcZ
      (∏ n ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.shifts U η, (Polynomial.X - Polynomial.C (((n * e * l : ℤ) : K)))) = 0 := by
    ext w
    have h1 := aeval_intertwine D.Zl.subtype D.LcZ D.Lc (fun _ => rfl)
      (∏ n ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.shifts U η, (Polynomial.X - Polynomial.C (((n * e * l : ℤ) : K)))) w
    simp only [Submodule.subtype_apply] at h1
    rw [LinearMap.zero_apply, Submodule.coe_zero, h1]
    exact hann _ (Submodule.mem_inf.1 w.2).1
  have hinj : Function.Injective (fun n : ℤ => ((n * e * l : ℤ) : K)) := by
    intro m n h
    have h1 : m * e * l = n * e * l := Int.cast_injective h
    exact mul_right_cancel₀ he0 (mul_right_cancel₀ hl0 h1)
  exact semisimple_of_aeval D.LcZ _ _ hinj hZ

end GlobalTheory.LcSemisimple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaLocalOddResidueOfLieAlgebra
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

section Assembly

variable {K K' : UQ}

def prodEquiv (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    ((overExt φ B₁ ((RingHom.fst B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.fst (hψ e))
        (fun e => congrArg Prod.fst (hσ e))).prod
      (overExt φ B₂ ((RingHom.snd B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.snd (hψ e))
        (fun e => congrArg Prod.snd (hσ e)))).A ≃ₐ[K'.E] (overExt φ (B₁.prod B₂) ψ hψ hσ).A :=
  { RingEquiv.refl (B₁.A × B₂.A) with commutes' := fun _ => rfl }

theorem prodEquiv_isIso (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    Orbit.IsIso (prodEquiv φ B₁ B₂ ψ hψ hσ) :=
  ⟨fun _ => rfl, rfl⟩

theorem prod_unitary (B₁ B₂ : InvAlg K) (hu₁ : B₁.g * B₁.σ B₁.g = 1) (hu₂ : B₂.g * B₂.σ B₂.g = 1) :
    (B₁.prod B₂).g * (B₁.prod B₂).σ (B₁.prod B₂).g = 1 :=
  Prod.ext hu₁ hu₂

theorem prod_integral (B₁ B₂ : InvAlg K) (hi₁ : IsIntegral K.O B₁.g) (hi₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g := by
  obtain ⟨p₁, hp₁, e₁⟩ := hi₁
  obtain ⟨p₂, hp₂, e₂⟩ := hi₂
  refine ⟨p₁ * p₂, hp₁.mul hp₂, ?_⟩
  rw [← aeval_def] at e₁ e₂ ⊢
  have h1 : (aeval (B₁.prod B₂).g (p₁ * p₂)).1 = aeval B₁.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  have h2 : (aeval (B₁.prod B₂).g (p₁ * p₂)).2 = aeval B₂.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  refine Prod.ext ?_ ?_
  · rw [h1, map_mul, e₁, zero_mul]; rfl
  · rw [h2, map_mul, e₂, mul_zero]; rfl

end Assembly

theorem unitLemma_local_of_lie : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by
  intro hL K hK B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  have hsepP : (B₁.prod B₂).P.Separable := by rw [Orbit.prod_P]; exact hsep
  have huP := prod_unitary B₁ B₂ hu₁ hu₂
  have hiP := prod_integral B₁ B₂ hi₁ hi₂
  obtain ⟨d, hd, hcard⟩ := GlobalTheory.T.card_residueField_adjoin_unitary_prod K hK B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  obtain ⟨K', φ, hq, hc, hv, hodd, hfin, hz⟩ := GlobalTheory.T.exists_unramified_odd_degree_quadratic_local_ext K d hd
  have hU : IsUnrExt K K' d φ := ⟨hq, hc, hv, hodd, hfin⟩
  obtain ⟨ψ, hψ, hσ, hO, s, hs, hres⟩ := GlobalTheory.T.exists_unramified_involution_field_embedding K hK (B₁.prod B₂) huP hsepP hiP hl d hcard K' φ hU hz
  obtain ⟨Q, hQ1, hQ2⟩ := GlobalTheory.T.charpoly_overExt_integral_reduction_pow K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO hl hsepP hiP s hres
  have hiso := prodEquiv_isIso φ B₁ B₂ ψ hψ hσ
  set ψ₁ := (RingHom.fst B₁.A B₂.A).comp ψ with hψ₁
  set ψ₂ := (RingHom.snd B₁.A B₂.A).comp ψ with hψ₂
  have h₁ : ∀ e, ψ₁ (φ e) = algebraMap K.E B₁.A e := fun e => congrArg Prod.fst (hψ e)
  have h₁' : ∀ e, B₁.σ (ψ₁ e) = ψ₁ (K'.c e) := fun e => congrArg Prod.fst (hσ e)
  have h₂ : ∀ e, ψ₂ (φ e) = algebraMap K.E B₂.A e := fun e => congrArg Prod.snd (hψ e)
  have h₂' : ∀ e, B₂.σ (ψ₂ e) = ψ₂ (K'.c e) := fun e => congrArg Prod.snd (hσ e)
  set C₁ := overExt φ B₁ ψ₁ h₁ h₁' with hC₁
  set C₂ := overExt φ B₂ ψ₂ h₂ h₂' with hC₂
  have hPP : C₁.P * C₂.P = (overExt φ (B₁.prod B₂) ψ hψ hσ).P := by
    rw [← Orbit.prod_P, ← hiso.charpoly_eq_of_isIso]
  have hO₁ : ∀ y : K'.O, ψ₁ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).1 ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO₂ : ∀ y : K'.O, ψ₂ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).2 ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO' : ∀ y : K'.O, (ψ₁.prod ψ₂) (algebraMap K'.O K'.E y) ∈
      Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A) := fun y => hO y
  have hQ : ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = C₁.P * C₂.P ∧
      Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O (s : K'.O))) ^ Q.natDegree :=
    ⟨Q, hQ1.trans hPP.symm, hQ2⟩

  have hsep' : (C₁.P * C₂.P).Separable := by
    rw [hPP]
    exact GlobalTheory.T.separable_charpoly_invAlgBaseChangeUnramified K K' d φ hU (B₁.prod B₂) ψ hψ hσ hsepP
  have hId := GlobalTheory.T.unitLemma_residually_unipotent_via_cayley hL K' (hodd hK) C₁ C₂ hu₁ hu₂ hsep' s hs hQ

  have hst : ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e)
      (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)),
      (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) →
      (overExt φ B ψ hψ hσ).stSum = B.stSum := by
    intro B ψ hψ hσ hO'
    unfold InvAlg.stSum
    exact finsum_congr fun k => GlobalTheory.T.unramifiedBaseChange_latticeCount_eq K K' d φ hU B ψ hψ hσ hO' _
  have hkap : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
    unfold InvAlg.kapSum
    refine finsum_congr fun k => ?_
    have hN : (C₁.prod C₂).N k.rep = (B₁.prod B₂).N k.rep := by
      rw [← hiso.N_eq]
      exact GlobalTheory.T.unramifiedBaseChange_latticeCount_eq K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO _
    rw [hN]
    congr 1
    set x := (Quot.out k).1 with hx
    have hfix : B₁.σ ((x : (C₁.prod C₂).A).1) = (x : (C₁.prod C₂).A).1 := congrArg Prod.fst (Quot.out k).2
    let x₁ : B₁.Aˣ := Units.map (MonoidHom.fst B₁.A B₂.A) x
    have := GlobalTheory.T.eta_gramDet_invAlgBaseChangeUnramified_odd K K' d φ hU hd B₁ ψ₁ h₁ h₁' x₁ hfix
    exact this
  have hres' := GlobalTheory.T.val_resultant_eq_degree_mul_unramifiedExt K K' d φ hU hd B₁ B₂ ψ₁ ψ₂ h₁ h₁' h₂ h₂' hO' hsep s hQ
  unfold InvAlg.Identity at hId ⊢
  rw [hkap, hst B₁ ψ₁ h₁ h₁' hO₁, hst B₂ ψ₂ h₂ h₂' hO₂] at hId
  rw [← hId, hres', hq]
  congr 1
  obtain ⟨m, rfl⟩ := hd
  push_cast
  rw [show -((2 * (m : ℤ) + 1) * val K'.O (resultant C₁.P C₂.P)) =
      (2 * (m : ℤ) + 1) * (-val K'.O (resultant C₁.P C₂.P)) by ring, zpow_mul]
  congr 1
  rw [show (2 * (m : ℤ) + 1) = ((2 * m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, Odd.neg_pow ⟨m, rfl⟩]

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZetaSeriesHigherTermsMemLPowBreuilKisin
section
noncomputable section

namespace GlobalTheory

open PowerSeries GlobalTheory.BK

theorem nat_mul_add_le_pow {l : ℕ} (hl : 2 ≤ l) (n : ℕ) : n * l + l ≤ l ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have h1 := Nat.mul_le_mul_right l ih
    have h2 := Nat.mul_le_mul_left (n * l + l) hl
    nlinarith

theorem zeta_add_lphi_conn_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → η < H → 14 * H < l → E K l e ^ η • y₀ ∈ D.M → ∃ r ∈ D.MM, D.zeta ((X : K⟦X⟧) ^ e • y₀) + D.lphi (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (l : K) ^ (l - 14 * H) • r := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y₀ hη hηH hHl hy₀
  set y : Vec K a ι := (X : K⟦X⟧) ^ e • y₀ with hy
  set A := l - 14 * H with hA
  have hl0 : (l : K) ≠ 0 := l_ne_zero (K := K) l
  have hlA : (l : K) ^ A ≠ 0 := pow_ne_zero _ hl0
  set c : K := ((l : K) ^ A)⁻¹ with hc
  set w : Vec K a ι := c • (D.zeta y + D.lphi (D.conn y)) with hw
  let t : ℕ → Vec K a ι := fun n => -(c • (D.lphi ^ (n + 2)) (D.conn y))
  have hterm : ∀ n, ∃ v ∈ D.MM, t n = (l : K) ^ n • v := by
    intro n
    obtain ⟨w₁, hw₁, h₁⟩ := GlobalTheory.T.prime_pow_smul_connection_series_term_mem_lattice O K l e a ι η H D y₀ hη hy₀ (n + 1)
    obtain ⟨w', hw', h₂⟩ := GlobalTheory.T.exists_X_pow_smul_eq_prime_pow_smul_phiModule O K l e a ι D.toPhiMod (n + 1) w₁ hw₁
    set B := H + 2 * η + (n + 1) * (η - 1) with hB
    have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
    have hineq : B + A + n ≤ l ^ (n + 1) := by
      have h1 := nat_mul_add_le_pow hl2 n
      have h2 : (n + 1) * (η - 1) ≤ (n + 1) * H := Nat.mul_le_mul_left _ (by omega)
      have h3 : n * (H + 1) ≤ n * l := Nat.mul_le_mul_left _ (by omega)
      have h4 : (n + 1) * H = n * H + H := by ring
      have h5 : n * (H + 1) = n * H + n := by ring
      omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hineq
    rw [h₂, hd, show B + A + n + d = B + (A + (n + d)) by ring, pow_add (l : K) B, mul_smul] at h₁
    have h₃ := congrArg (fun v => ((l : K) ^ B)⁻¹ • v) h₁
    simp only [inv_smul_smul₀ (pow_ne_zero B hl0)] at h₃
    refine ⟨-((l : K) ^ d • w'), neg_mem (PhiMod.l_pow_smul_mem_MM _ d hw'), ?_⟩
    change -(c • (D.lphi ^ (n + 1 + 1)) (D.conn y)) = _
    rw [h₃, pow_add, mul_smul, hc, inv_smul_smul₀ hlA, pow_add, mul_smul, smul_neg]
  have hpart : ∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow K a ι m := by
    intro m
    have key := D.zeta_add_sum_mem y (m + 1)
    rw [Finset.sum_range_succ'] at key
    have heq : w - ∑ n ∈ Finset.range m, t n = c • (D.zeta y + (∑ n ∈ Finset.range m,
        (D.lphi ^ (n + 1 + 1)) (D.conn y) + (D.lphi ^ (0 + 1)) (D.conn y))) := by
      simp only [t, hw, Finset.sum_neg_distrib, sub_neg_eq_add, zero_add, pow_one, smul_add,
        Finset.smul_sum]
      abel
    rw [heq]
    exact Submodule.smul_of_tower_mem _ c (uPow_anti (by omega) key)
  refine ⟨w, GlobalTheory.T.mem_phiModuleLattice_of_adic_series_prime_pow_terms O K l e a ι D.toPhiMod w t hterm hpart, ?_⟩
  rw [hw, hc, smul_inv_smul₀ hlA]

end GlobalTheory
end
end

