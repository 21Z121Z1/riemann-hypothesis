import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0275
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0357
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalBasisCoeffDiscExtension
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntSpanImageLatticeRegular
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem exists_zl_span_lattice_reads : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)), Continuous r → ∃ (d : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Continuous ρ ∧ Reads ρ r b e ∧ LinearIndependent ℚ_[l] b ∧ ∀ i, ∃ f : Γ →₀ ℤ_[l], b i = f.sum fun h c => zOm l c • (r h).val := by
  intro l _ Γ _ _ _ _ a r hr
  classical
  have hz : ∀ c : ℤ_[l], zOm l c = algebraMap ℤ_[l] (Om l) c := fun c =>
    (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l) c).symm
  have hsm : ∀ (c : ℤ_[l]) (x : Matrix (Fin a) (Fin a) (Om l)), c • x = zOm l c • x := by
    intro c x; ext i j; simp [Matrix.smul_apply, Algebra.smul_def, hz]
  have hsq : ∀ (c : ℤ_[l]) (x : Matrix (Fin a) (Fin a) (Om l)), c • x = (c : ℚ_[l]) • x := by
    intro c x; rw [hsm]; ext i j; simp [Matrix.smul_apply, Algebra.smul_def, zOm]
  let v : Γ → Matrix (Fin a) (Fin a) (Om l) := fun h => (r h).val
  let M : Submodule ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) := Submodule.span ℤ_[l] (Set.range v)

  obtain ⟨t, ht⟩ := GlobalTheory.zl_span_image_finite l Γ a r hr
  have hfg : M.FG := by
    refine ⟨t.image v, le_antisymm ?_ ?_⟩
    · rw [Finset.coe_image]; exact Submodule.span_mono (Set.image_subset_range _ _)
    · rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      obtain ⟨f', hf't, hf'⟩ := ht (Finsupp.single h 1)
      have hvh : v h = f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) •
          ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
        rw [← hf', Finsupp.sum_single_index (by simp)]
        simp [v]
      rw [SetLike.mem_coe, hvh]
      refine Submodule.sum_mem _ fun k hk => ?_
      have : ((algebraMap ℚ_[l] (PadicAlgCl l)) (f' k : ℚ_[l])) •
          ((r k : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) = f' k • v k := by
        rw [hsm]; rfl
      refine (show _ ∈ _ from ?_)
      beta_reduce
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem v (hf't hk))))
  haveI : Module.Finite ℤ_[l] M := Module.Finite.iff_fg.mpr hfg
  haveI : Module.IsTorsionFree ℤ_[l] M := Module.IsTorsionFree.of_smul_eq_zero fun c m h => by
    have h' : (c : ℚ_[l]) • (m : Matrix (Fin a) (Fin a) (Om l)) = 0 := by
      rw [← hsq]; exact congrArg Subtype.val h
    rcases smul_eq_zero.1 h' with h0 | h0
    · left; exact Subtype.ext h0
    · right; exact Subtype.ext h0
  haveI : Module.Free ℤ_[l] M := Module.free_of_finite_type_torsion_free'
  let d := Module.finrank ℤ_[l] M
  let B : Module.Basis (Fin d) ℤ_[l] M := Module.finBasis ℤ_[l] M

  have hstab : ∀ (g : Γ) (x : Matrix (Fin a) (Fin a) (Om l)), x ∈ M → v g * x ∈ M := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, rfl⟩ := hy
      exact Submodule.subset_span ⟨g * h, by simp [v, map_mul]⟩
    | zero => simp
    | add y z _ _ hy hz => rw [Matrix.mul_add]; exact M.add_mem hy hz
    | smul c y _ hy => rw [Matrix.mul_smul]; exact M.smul_mem c hy
  let Lm : Γ → Module.End ℤ_[l] M := fun g =>
    { toFun := fun x => ⟨v g * x, hstab g x x.2⟩
      map_add' := fun x y => Subtype.ext (Matrix.mul_add _ _ _)
      map_smul' := fun c x => Subtype.ext (Matrix.mul_smul _ _ _) }
  let L : Γ →* Module.End ℤ_[l] M :=
    { toFun := Lm
      map_one' := LinearMap.ext fun x => Subtype.ext (by simp [Lm, v])
      map_mul' := fun g h => LinearMap.ext fun x => Subtype.ext (by simp [Lm, v, map_mul, Matrix.mul_assoc]) }
  let ρ₀ : Γ →* Matrix (Fin d) (Fin d) ℤ_[l] :=
    (LinearMap.toMatrixAlgEquiv B).toAlgHom.toRingHom.toMonoidHom.comp L
  let ρ : Γ →* GL (Fin d) ℤ_[l] := ρ₀.toHomUnits
  have hρ : ∀ g i j, (ρ g).val i j = B.repr (Lm g (B j)) i := by
    intro g i j
    exact LinearMap.toMatrixAlgEquiv_apply B (L g) i j
  let b : Fin d → Matrix (Fin a) (Fin a) (Om l) := fun i => (B i : Matrix (Fin a) (Fin a) (Om l))
  have hrepr : ∀ x : M, ∑ i, zOm l (B.repr x i) • b i = x := by
    intro x
    have := congrArg Subtype.val (B.sum_repr x)
    rw [Submodule.coe_sum] at this
    simpa [b, hsm] using this
  have h1M : (1 : Matrix (Fin a) (Fin a) (Om l)) ∈ M := Submodule.subset_span ⟨1, by simp [v]⟩
  let e : Fin d → ℤ_[l] := fun i => B.repr ⟨1, h1M⟩ i
  have hreads : Reads ρ r b e := by
    refine ⟨fun g j => ?_, ?_⟩
    · simp_rw [hρ]
      rw [hrepr]
      rfl
    · exact hrepr ⟨1, h1M⟩

  have hliZ : LinearIndependent ℤ_[l] b := B.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent ℚ_[l] b := (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 hliZ
  refine ⟨d, ρ, b, e, ?_, hreads, hli, fun i => ?_⟩
  rotate_left
  · obtain ⟨f, hf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 (B i).2
    refine ⟨f, ?_⟩
    show (B i : Matrix (Fin a) (Fin a) (Om l)) = _
    rw [← hf]
    simp [Finsupp.sum, hsm, v]

  let Wq := Submodule.span ℚ_[l] (Set.range b)
  let Bq : Module.Basis (Fin d) ℚ_[l] Wq := Module.Basis.span hli
  haveI : FiniteDimensional ℚ_[l] Wq := Module.Finite.of_basis Bq
  have hmemW : ∀ x : M, (x : Matrix (Fin a) (Fin a) (Om l)) ∈ Wq := by
    intro x
    rw [← hrepr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hsm, hsq]
    exact Wq.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcoord : ∀ x : M, ∀ i, ((B.repr x i : ℤ_[l]) : ℚ_[l]) = Bq.repr ⟨x, hmemW x⟩ i := by
    intro x i
    have hx : (⟨x, hmemW x⟩ : Wq) = ∑ k, ((B.repr x k : ℤ_[l]) : ℚ_[l]) • Bq k := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      conv_lhs => rw [← hrepr x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Submodule.coe_smul, Module.Basis.span_apply, ← hsm, hsq]
    rw [hx, Module.Basis.repr_sum_self]
  have hcv : Continuous v := Units.continuous_val.comp hr
  have hval : Continuous fun g => (ρ g).val := by
    refine continuous_matrix fun i j => ?_
    have : (fun g => (((ρ g).val i j : ℤ_[l]) : ℚ_[l])) = fun g => Bq.coord i ⟨v g * b j, hmemW (Lm g (B j))⟩ := by
      funext g
      rw [hρ, hcoord]
      rfl
    have hcq : Continuous (fun g => (((ρ g).val i j : ℤ_[l]) : ℚ_[l])) := by
      rw [this]
      refine (LinearMap.continuous_of_finiteDimensional (Bq.coord i)).comp ?_
      exact (hcv.mul continuous_const).subtype_mk _
    exact continuous_induced_rng.2 hcq
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have : (fun g => ((ρ g)⁻¹ : GL (Fin d) ℤ_[l]).val) = (fun g => (ρ g).val) ∘ fun g => g⁻¹ := by
    funext g; simp [map_inv]
  rw [this]
  exact hval.comp continuous_inv

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulDescPochhammerEulerEqEisensteinPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.BK GlobalTheory.BKReal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem N_sub_smul_mem_A {c : K} (hc : ‖c‖ ≤ 1) {g : K⟦X⟧} (hg : g ∈ A O K) :
    N K g - c • g ∈ A O K := fun n => by
  rw [map_sub, coeff_N, coeff_smul, smul_eq_mul, ← sub_mul, norm_mul]
  rw [sub_eq_add_neg]
  refine mul_le_one₀ ?_ (norm_nonneg _) (hg n)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  rw [norm_neg]
  exact
    max_le (IsUltrametricDist.norm_natCast_le_one K n) hc

theorem exists_N_sub_smul_E_pow_mul (l e : ℕ) {c : K} (hc : ‖c‖ ≤ 1) {g : K⟦X⟧} (hg : g ∈ A O K)
    (j : ℕ) : ∃ g' ∈ A O K,
      N K (E K l e ^ j * g) - c • (E K l e ^ j * g) = E K l e ^ (j - 1) * g' := by
  cases j with
  | zero => exact ⟨_, N_sub_smul_mem_A hc hg, by simp⟩
  | succ j =>
    refine ⟨((j + 1 : ℕ) : K⟦X⟧) * ((e : K⟦X⟧) * X ^ e) * g + E K l e * (N K g - c • g),
      (A O K).add_mem ((A O K).mul_mem ((A O K).mul_mem (natCast_mem _ _)
        ((A O K).mul_mem (natCast_mem _ _) ((A O K).pow_mem HasU.X_mem e))) hg)
        ((A O K).mul_mem (E_mem l e _) (N_sub_smul_mem_A hc hg)), ?_⟩
    rw [Derivation.leibniz, Derivation.leibniz_pow, N_E, Nat.add_sub_cancel]
    simp only [smul_eq_mul, nsmul_eq_mul, smul_eq_C_mul]
    push_cast
    ring

theorem exists_aeval_comp_E_pow_mul (l e i : ℕ) : ∀ (m : ℕ) {g : K⟦X⟧}, g ∈ A O K →
    ∃ g' ∈ A O K, Polynomial.aeval (N K).toLinearMap
      ((descPochhammer K i).comp (Polynomial.X - 1)) (E K l e ^ m * g) = E K l e ^ (m - i) * g' := by
  induction i with
  | zero => intro m g hg; exact ⟨g, hg, by simp⟩
  | succ i ih =>
    intro m g hg
    obtain ⟨g₁, hg₁, h₁⟩ := exists_N_sub_smul_E_pow_mul (O := O) l e (c := ((i + 1 : ℕ) : K))
      (IsUltrametricDist.norm_natCast_le_one K _) hg m
    obtain ⟨g₂, hg₂, h₂⟩ := ih (m - 1) hg₁
    refine ⟨g₂, hg₂, ?_⟩
    have h₃ : ∀ x : K⟦X⟧, Polynomial.aeval (N K).toLinearMap
        ((Polynomial.X - (i : Polynomial K)).comp (Polynomial.X - 1)) x = N K x - ((i + 1 : ℕ) : K) • x := by
      intro x
      rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.natCast_comp, map_sub, map_sub,
        Polynomial.aeval_X, map_natCast, map_one, LinearMap.sub_apply, LinearMap.sub_apply,
        Module.End.natCast_apply, Module.End.one_apply, Derivation.coeFn_coe]
      push_cast
      rw [add_smul, one_smul, Nat.cast_smul_eq_nsmul]
      abel
    rw [descPochhammer_succ_right, Polynomial.mul_comp, map_mul (Polynomial.aeval _), Module.End.mul_apply, h₃, h₁, h₂,
      Nat.sub_sub, add_comm 1 i]

theorem exists_l_pow_mul_descN_eq_E_pow_mul : ∀ (l e : ℕ) (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (f h : K⟦X⟧) (k m : ℕ), h ∈ A O K →
    (l : K⟦X⟧) ^ k * N K f = E K l e ^ m * h → ∀ i : ℕ, 1 ≤ i →
    ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i f = E K l e ^ (m + 1 - i) * h' := by
  intro l e O K _ _ _ _ _ f h k m hh hf i hi
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
  obtain ⟨h', hh', h₁⟩ := exists_aeval_comp_E_pow_mul (O := O) l e i m hh
  refine ⟨h', hh', ?_⟩
  have hl : (l : K⟦X⟧) ^ k = C ((l : K) ^ k) := by simp
  rw [Nat.add_sub_add_right, ← h₁, ← hf, descN, descPochhammer_succ_left, mul_comm (Polynomial.X : Polynomial K), map_mul (Polynomial.aeval _),
    Polynomial.aeval_X, Module.End.mul_apply, hl, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
  rfl

end GlobalTheory.BKReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesRingHomOfIsAdicComplete
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.PowerSeriesEval

theorem mk_eval₂_trunc_coe {W C : Type} [CommRing W] [CommRing C] (ω : W →+* C) (v : C)
    (I : Ideal C) {K : ℕ} (hK : v ^ K ∈ I) (p : Polynomial W) :
    Ideal.Quotient.mk I ((PowerSeries.trunc K (p : W⟦X⟧)).eval₂ ω v) =
      Ideal.Quotient.mk I (p.eval₂ ω v) := by
  have hdvd : (Polynomial.X : Polynomial W) ^ K ∣ p - PowerSeries.trunc K (p : W⟦X⟧) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hd, Polynomial.coeff_coe, sub_self]
  obtain ⟨q, hq⟩ := hdvd
  generalize PowerSeries.trunc K (p : W⟦X⟧) = t at hq ⊢
  have hp : p = t + Polynomial.X ^ K * q := by
    rw [← hq]; ring
  rw [Ideal.Quotient.eq, hp, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow]
  have : t.eval₂ ω v - (t.eval₂ ω v + v ^ K * q.eval₂ ω v) = -(v ^ K * q.eval₂ ω v) := by ring
  rw [this]
  exact I.neg_mem (I.mul_mem_right _ hK)

noncomputable def truncEval {W C : Type} [CommRing W] [CommRing C] (ω : W →+* C) (v : C)
    (I : Ideal C) (K : ℕ) (hK : v ^ (K + 1) ∈ I) : W⟦X⟧ →+* C ⧸ I where
  toFun f := Ideal.Quotient.mk I ((PowerSeries.trunc (K + 1) f).eval₂ ω v)
  map_one' := by simp
  map_mul' f g := by
    rw [← PowerSeries.trunc_trunc_mul_trunc, ← Polynomial.coe_mul, mk_eval₂_trunc_coe ω v I hK,
      Polynomial.eval₂_mul, map_mul]
  map_zero' := by simp
  map_add' f g := by simp [Polynomial.eval₂_add]

theorem truncEval_apply {W C : Type} [CommRing W] [CommRing C] (ω : W →+* C) (v : C)
    (I : Ideal C) (K : ℕ) (hK : v ^ (K + 1) ∈ I) (f : W⟦X⟧) :
    truncEval ω v I K hK f = Ideal.Quotient.mk I ((PowerSeries.trunc (K + 1) f).eval₂ ω v) := rfl

end GlobalTheory.PowerSeriesEval

open GlobalTheory.PowerSeriesEval in
theorem GlobalTheory.PowerSeriesEval.exists_ringHom_powerSeries :
    ∀ (W : Type) [CommRing W] (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C →
      ∀ (ω : W →+* C) (v : C) (e : ℕ), v ^ e ∈ J →
        ∃ σ : W⟦X⟧ →+* C, (∀ w, σ (PowerSeries.C w) = ω w) ∧ σ X = v := by
  intro W _ C _ J hJ ω v e he

  have hN : v ^ (e + 1) ∈ J := by rw [pow_succ]; exact J.mul_mem_right _ he
  have hK : ∀ n : ℕ, v ^ ((e + 1) * n + 1) ∈ J ^ n := fun n => by
    rw [pow_succ, pow_mul]
    exact (J ^ n).mul_mem_right _ (Ideal.pow_mem_pow hN n)
  let f : (n : ℕ) → W⟦X⟧ →+* C ⧸ J ^ n := fun n => truncEval ω v (J ^ n) ((e + 1) * n) (hK n)
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (f n) = f m := by
    intro m n hle
    ext g
    simp only [f, RingHom.comp_apply, truncEval_apply, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [← mk_eval₂_trunc_coe ω v (J ^ m) (hK m),
      PowerSeries.trunc_trunc_of_le _ (Nat.succ_le_succ (Nat.mul_le_mul_left _ hle))]
  refine ⟨IsAdicComplete.liftRingHom J f hf, fun w => ?_, ?_⟩
  · have := IsHausdorff.funext' (R := Unit) J (f := fun _ => IsAdicComplete.liftRingHom J f hf (PowerSeries.C w))
      (g := fun _ => ω w) (fun n _ => by
        rw [IsAdicComplete.mk_liftRingHom]
        simp [f, truncEval_apply])
    exact congrFun this ()
  · have := IsHausdorff.funext' (R := Unit) J (f := fun _ => IsAdicComplete.liftRingHom J f hf X)
      (g := fun _ => v) (fun n _ => by
        rw [IsAdicComplete.mk_liftRingHom]
        simp only [f, truncEval_apply]
        rcases n with _ | n
        · rw [Ideal.Quotient.eq, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
        · rw [PowerSeries.trunc_X_of (Nat.succ_le_succ (Nat.mul_pos (Nat.succ_pos e) (Nat.succ_pos n))),
            Polynomial.eval₂_X])
    exact congrFun this ()
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowDvdModEisensteinOfTheta
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LiftDiv

theorem dvd_mod_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (s : bk.S) (n : ℕ) (y : OC l), Per.θ l (bk.ev s) = (l : OC l) ^ n * y → ∃ s' t : bk.S, s = (l : bk.S) ^ n * s' + bk.E * t := by
  intro l _ K bk s n y h
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ s) with hr
  have hθ : Per.θ l (bk.ev s) = intToOC K r := bk.θ_ev r s (by rw [hr, RingEquiv.apply_symm_apply])
  have hC : ((((r : ↥K.1) : Om l)) : ℂ_[l]) = (l : ℂ_[l]) ^ n * ((y : OC l) : ℂ_[l]) := by
    rw [← coe_intToOC, ← hθ, h]
    push_cast
    rfl
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hnorm : ‖((r : ↥K.1) : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ n := by
    rw [← PadicComplex.norm_extends, hC, norm_mul, norm_pow, GlobalTheory.UnrWitt.norm_l_C]
    exact mul_le_of_le_one_right (by positivity) (GlobalTheory.UnrWitt.norm_OC_le y)
  set q : ↥K.1 := (r : ↥K.1) / (l : ↥K.1) ^ n with hq
  have hqO : ((q : ↥K.1) : Om l) = ((r : ↥K.1) : Om l) / (l : Om l) ^ n := by
    rw [hq]; push_cast; rfl
  have hq1 : ‖((q : ↥K.1) : Om l)‖ ≤ 1 := by
    rw [hqO, norm_div, norm_pow, GlobalTheory.UnrWitt.norm_l_Om]
    rw [div_le_one (by positivity)]
    exact hnorm
  let r' : ↥(OL K) := ⟨q, GlobalTheory.UnrWitt.mem_OL_of_norm_le K q hq1⟩
  have hrr : r = (l : ↥(OL K)) ^ n * r' := by
    apply Subtype.ext
    apply Subtype.ext
    have : ((((l : ↥(OL K)) ^ n * r' : ↥(OL K)) : ↥K.1) : Om l) = (l : Om l) ^ n * ((q : ↥K.1) : Om l) := by
      push_cast; rfl
    rw [this, hqO, mul_div_cancel₀ _ (pow_ne_zero _ hl0)]
  obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (bk.str r')
  have hmk : Ideal.Quotient.mk (Ideal.span {bk.E}) (s - (l : bk.S) ^ n * s') = 0 := by
    have e1 : Ideal.Quotient.mk (Ideal.span {bk.E}) s = bk.str r := by
      rw [hr, RingEquiv.apply_symm_apply]
    rw [map_sub, map_mul, map_pow, map_natCast, e1, hs', hrr, map_mul, map_pow, map_natCast, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)
  exact ⟨s', t, by rw [mul_comm bk.E t, ht]; ring⟩

end GlobalTheory.LiftDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingHomExtendIsAdicCompletionMap
section
namespace GlobalTheory.BSP

theorem exists_ringHom_comp_of_isCompl : ∀ (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C]
    (i : L →+* Q) (J : Ideal L) (JC : Ideal C), IsCompl i J → IsAdicComplete JC C →
    ∀ g : L →+* C, J.map g ≤ JC → ∃ h : Q →+* C, h.comp i = g := by
  intro L _ Q _ C _ i J JC hi hC g hg
  haveI := hC

  let ψ : (n : ℕ) → L →+* Q ⧸ (J ^ n).map i := fun n => (Ideal.Quotient.mk _).comp i
  have hψ : ∀ n, Function.Surjective (ψ n) := by
    intro n y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hi.surj x n
    exact ⟨a, (Ideal.Quotient.eq.mpr ha).symm⟩
  have hker : ∀ n, RingHom.ker (ψ n) ≤ RingHom.ker ((Ideal.Quotient.mk (JC ^ n)).comp g) := by
    intro n a ha
    have h1 : a ∈ J ^ n := hi.ker a n (Ideal.Quotient.eq_zero_iff_mem.mp ha)
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    have h2 : g a ∈ (J ^ n).map g := Ideal.mem_map_of_mem g h1
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono hg n h2
  let F : (n : ℕ) → Q ⧸ (J ^ n).map i →+* C ⧸ JC ^ n := fun n =>
    (Ideal.Quotient.lift (RingHom.ker (ψ n)) ((Ideal.Quotient.mk (JC ^ n)).comp g) (hker n)).comp
      (RingHom.quotientKerEquivOfSurjective (hψ n)).symm.toRingHom
  have hF : ∀ n a, F n (ψ n a) = Ideal.Quotient.mk (JC ^ n) (g a) := by
    intro n a
    have : (RingHom.quotientKerEquivOfSurjective (hψ n)).symm (ψ n a) = Ideal.Quotient.mk _ a := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [F, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this,
      Ideal.Quotient.lift_mk]
    rfl
  let f : (n : ℕ) → Q →+* C ⧸ JC ^ n := fun n => (F n).comp (Ideal.Quotient.mk _)
  have hfa : ∀ n x a, x - i a ∈ (J ^ n).map i → f n x = Ideal.Quotient.mk (JC ^ n) (g a) := by
    intro n x a h
    have : Ideal.Quotient.mk ((J ^ n).map i) x = ψ n a := Ideal.Quotient.eq.mpr h
    simp only [f, RingHom.comp_apply, this, hF]
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow JC hle).comp (f n) = f m := by
    intro m n hle
    refine RingHom.ext fun x => ?_
    obtain ⟨a, ha⟩ := hi.surj x n
    have ha' : x - i a ∈ (J ^ m).map i := Ideal.map_mono (Ideal.pow_le_pow_right hle) ha
    rw [RingHom.comp_apply, hfa n x a ha, hfa m x a ha']
    rfl
  refine ⟨IsAdicComplete.liftRingHom JC f hf, RingHom.ext fun a => ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero]
  refine IsHausdorff.haus' (I := JC) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom,
    hfa n (i a) a (by simp)]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableSpanningFinsetMatrices
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory

theorem exists_stable_spanning_finset : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (Om l)) (L : FinExt l), Continuous ρ → (∀ g i j, (ρ g).val i j ∈ L.1) → ∃ t : Finset (Matrix (Fin a) (Fin a) (Om l)), (∀ x ∈ t, ∀ i j, x i j ∈ L.1) ∧ (∀ x : Matrix (Fin a) (Fin a) (Om l), (∀ i j, x i j ∈ L.1) → x ∈ Submodule.span ℚ_[l] (t : Set (Matrix (Fin a) (Fin a) (Om l)))) ∧ (∃ c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t, zOm l (c y) • y = 1) ∧ ∀ g, ∀ x ∈ t, ∃ c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], (ρ g).val * x = ∑ y ∈ t, zOm l (c y) • y := by
  intro l _ Γ _ _ _ _ a ρ L hρ hL
  classical
  obtain ⟨t₀, ht₀⟩ := zl_span_image_finite l Γ a ρ hρ
  let e : Matrix (Fin a) (Fin a) L.1 →ₗ[ℚ_[l]] Matrix (Fin a) (Fin a) (Om l) :=
    LinearMap.mapMatrix L.1.val.toLinearMap
  haveI : FiniteDimensional ℚ_[l] L.1 := L.2
  let bM := Module.finBasis ℚ_[l] (Matrix (Fin a) (Fin a) L.1)
  let B : Finset (Matrix (Fin a) (Fin a) (Om l)) := insert 1 (Finset.univ.image (fun k => e (bM k)))
  let t₁ : Finset Γ := insert 1 t₀
  let t : Finset (Matrix (Fin a) (Fin a) (Om l)) := (t₁ ×ˢ B).image (fun p => (ρ p.1).val * p.2)
  have hBL : ∀ b ∈ B, ∀ i j, b i j ∈ L.1 := by
    intro b hb i j
    rcases Finset.mem_insert.mp hb with rfl | hb
    · by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hb
      exact (bM k i j).2
  have hmemt : ∀ h ∈ t₁, ∀ b ∈ B, (ρ h).val * b ∈ t := fun h hh b hb =>
    Finset.mem_image.mpr ⟨(h, b), Finset.mem_product.mpr ⟨hh, hb⟩, rfl⟩
  have hBt : ∀ b ∈ B, b ∈ t := fun b hb => by
    have := hmemt 1 (Finset.mem_insert_self _ _) b hb
    simpa using this
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · intro x hx i j
    obtain ⟨⟨h, b⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    have hb := (Finset.mem_product.mp hp).2
    simp only [Matrix.mul_apply]
    exact L.1.sum_mem fun k _ => L.1.mul_mem (hL h i k) (hBL b hb k j)
  · intro x hx
    have hxe : x = e (fun i j => ⟨x i j, hx i j⟩) := by ext i j; rfl
    have hsp : (fun i j => (⟨x i j, hx i j⟩ : L.1)) ∈ Submodule.span ℚ_[l] (Set.range bM) := by
      rw [bM.span_eq]; trivial
    have h2 : e (fun i j => ⟨x i j, hx i j⟩) ∈ Submodule.span ℚ_[l] (e '' Set.range bM) := by
      rw [Submodule.span_image]; exact Submodule.mem_map_of_mem hsp
    rw [hxe]
    refine Submodule.span_mono ?_ h2
    rintro y ⟨z, ⟨k, rfl⟩, rfl⟩
    exact hBt _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
  · refine ⟨fun y => if y = 1 then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (1 : Matrix (Fin a) (Fin a) (Om l))]
    · simp
    · intro y _ hy; simp [hy]
    · intro h1; exact absurd (hBt 1 (Finset.mem_insert_self _ _)) h1
  · intro g x hx
    obtain ⟨⟨h, b⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    have hb := (Finset.mem_product.mp hp).2
    obtain ⟨f', hf'sup, hf'⟩ := ht₀ (Finsupp.single (g * h) 1)
    have hgh : ((ρ (g * h) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) =
        f'.sum fun k c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) •
          ((ρ k : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
      rw [← hf', Finsupp.sum_single_index (by simp)]
      simp
    refine ⟨fun y => ∑ k ∈ f'.support with (ρ k).val * b = y, f' k, ?_⟩
    have hmaps : ∀ k ∈ f'.support, (ρ k).val * b ∈ t := fun k hk =>
      hmemt k (Finset.mem_insert_of_mem (hf'sup hk)) b hb
    calc (ρ g).val * ((ρ h).val * b) = (ρ (g * h)).val * b := by rw [map_mul, Units.val_mul, Matrix.mul_assoc]
      _ = ∑ k ∈ f'.support, zOm l (f' k) • ((ρ k).val * b) := by
          rw [hgh, Finsupp.sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.smul_mul]; rfl
      _ = ∑ y ∈ t, ∑ k ∈ f'.support with (ρ k).val * b = y, zOm l (f' k) • ((ρ k).val * b) :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ = ∑ y ∈ t, zOm l (∑ k ∈ f'.support with (ρ k).val * b = y, f' k) • y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [map_sum, Finset.sum_smul]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [(Finset.mem_filter.mp hk).2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalBasisCoeffDiscExtensionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_topologicalBasis_coeff_disc_extension : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ j : bk.DS ρ →+* Disc l (s X) ρ, IsDiscMap s j → ∃ cD : ι → (Disc l (s X) ρ →+ bk.DS ρ), (∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧ (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖) := by
  first | exact @GlobalTheory.BSP.exists_discCoeff | exact GlobalTheory.BSP.exists_discCoeff | (intros; apply GlobalTheory.BSP.exists_discCoeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteImageOfTrivialOnOpenStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_of_trivial_on_inf_isOpen : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (Q : Type) [Group Q] (ρ : ↥(GK K) →* Q) (J H : Subgroup ↥(GK K)), IsOpen (H : Set ↥(GK K)) → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set ↥(GK K))).Finite := by
  first | exact @GlobalTheory.GK.finite_image_of_trivial_on_open | exact GlobalTheory.GK.finite_image_of_trivial_on_open | (intros; apply GlobalTheory.GK.finite_image_of_trivial_on_open <;> assumption)
end

