import Mathlib
import Formalism.LocalToGlobal.Columns.BrpAevalScaleMonomial
import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrSep
import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0005
import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0007
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.GL3MeanSquares.HookFormulaTorsion.FibreCardinalityOfModuliMap

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.PDetAll
section
open MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

section Char

variable (K : Type) [Field K] [CharZero K] {n : ℕ} (χ : GL (Fin n) K →* K)

theorem glChar_ne_zero (g : GL (Fin n) K) : χ g ≠ 0 := by
  intro h
  have h1 : χ g * χ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem glChar_transvection (i j : Fin n) (hij : i ≠ j) (c : K) :
    χ (brpGL K (Matrix.transvection i j c) (brp_isUnit_transvection K i j hij c)) = 1 := by
  set T : K → GL (Fin n) K := fun c => brpGL K (Matrix.transvection i j c) (brp_isUnit_transvection K i j hij c) with hT
  have hdet2 : IsUnit (Matrix.diagonal (Function.update (1 : Fin n → K) i 2)).det := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  set D := brpGL K _ hdet2
  have h2 : T c * T c = T (2 * c) := by
    apply Units.ext
    simp only [hT, Units.val_mul, brpGL_coe]
    rw [Matrix.transvection_mul_transvection_same i j hij, two_mul]
  have hDT : D * T c = T (2 * c) * D := by
    apply Units.ext
    simp only [hT, D, Units.val_mul, brpGL_coe]
    exact brp_diag_transvection K i j hij c
  have e1 := congrArg χ hDT
  rw [map_mul, map_mul, mul_comm (χ (T (2 * c)))] at e1
  have e2 : χ (T c) = χ (T (2 * c)) := mul_left_cancel₀ (glChar_ne_zero K χ D) e1
  rw [← h2, map_mul] at e2
  have hx := glChar_ne_zero K χ (T c)
  have : χ (T c) * (χ (T c) - 1) = 0 := by rw [mul_sub, mul_one, ← e2, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hx
  · exact (sub_eq_zero.1 h)

theorem glChar_single_eq (a b : Fin n) (t : Kˣ) :
    χ (brpDiag K (Pi.mulSingle a t)) = χ (brpDiag K (Pi.mulSingle b t)) := by
  set P := brpGL K _ (brp_isUnit_perm K (Equiv.swap a b))
  have hP : P * brpDiag K (Pi.mulSingle a t) = brpDiag K (Pi.mulSingle b t) * P := by
    apply Units.ext
    simp only [P, Units.val_mul, brpGL_coe, brpDiag_coe]
    rw [brp_perm_diag]
    congr 2
    funext x
    simp only [Function.comp_apply, Pi.mulSingle_apply]
    by_cases hx : x = b
    · subst hx; simp
    · by_cases hxa : x = a
      · subst hxa
        rw [Equiv.swap_apply_left]
        simp [hx, Ne.symm hx]
      · rw [Equiv.swap_apply_of_ne_of_ne hxa hx]
        simp [hx, hxa]
  have e := congrArg χ hP
  rw [map_mul, map_mul, mul_comm (χ (brpDiag K (Pi.mulSingle b t)))] at e
  exact mul_left_cancel₀ (glChar_ne_zero K χ P) e

theorem glChar_diag_pow (N : ℤ) (hs : ∀ t : Kˣ, χ (brpSc K t) = (t : K) ^ N) (d : Fin n → Kˣ) :
    χ (brpDiag K d) ^ n = (∏ a, (d a : K)) ^ N := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  set a0 : Fin n := ⟨0, hn⟩
  set φ : Kˣ → K := fun t => χ (brpDiag K (Pi.mulSingle a0 t))
  have h1 : χ (brpDiag K d) = ∏ a, φ (d a) := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle d]
    change (χ.comp (brpDiag K)) _ = _
    rw [map_prod]
    exact Finset.prod_congr rfl fun a _ => glChar_single_eq K χ a a0 (d a)
  have h2 : ∀ t : Kˣ, φ t ^ n = (t : K) ^ N := by
    intro t
    have : φ t ^ n = ∏ a : Fin n, χ (brpDiag K (Pi.mulSingle a t)) := by
      rw [Finset.prod_congr rfl fun a _ => glChar_single_eq K χ a a0 t, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    rw [this]
    have hc : (∏ a : Fin n, Pi.mulSingle a t) = fun _ => t := Finset.univ_prod_mulSingle (fun _ : Fin n => t)
    have e : (∏ a : Fin n, χ (brpDiag K (Pi.mulSingle a t))) = (χ.comp (brpDiag K)) (∏ a : Fin n, Pi.mulSingle a t) := by
      rw [map_prod]; rfl
    rw [e, hc, MonoidHom.comp_apply, brpDiag_const, hs]
  rw [h1, ← Finset.prod_pow, Finset.prod_congr rfl fun a _ => h2 (d a), Finset.prod_zpow]

theorem glChar_list_transvec (L : List (Matrix.TransvectionStruct (Fin n) K)) :
    χ (L.map fun t => brpGL K t.toMatrix (by rw [t.det]; exact isUnit_one)).prod = 1 := by
  rw [map_list_prod, List.map_map]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx
  exact glChar_transvection K χ t.i t.j t.hij t.c

theorem glChar_pow (N : ℤ) (hs : ∀ t : Kˣ, χ (brpSc K t) = (t : K) ^ N) (g : GL (Fin n) K) :
    χ g ^ n = ((g : Matrix (Fin n) (Fin n) K).det) ^ N := by
  classical
  obtain ⟨L, L', D, hM⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix (Fin n) (Fin n) K)
  have hdet : (g : Matrix (Fin n) (Fin n) K).det = ∏ a, D a := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, brp_det_list_transvec, brp_det_list_transvec, Matrix.det_diagonal, one_mul, mul_one]
  have hD : ∀ a, D a ≠ 0 := by
    have h0 : (g : Matrix (Fin n) (Fin n) K).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
    rw [hdet] at h0
    exact fun a => (Finset.prod_ne_zero_iff.1 h0) a (Finset.mem_univ a)
  set Du : Fin n → Kˣ := fun a => Units.mk0 (D a) (hD a)
  have hg : g = (L.map fun t => brpGL K t.toMatrix (by rw [t.det]; exact isUnit_one)).prod * brpDiag K Du *
      (L'.map fun t => brpGL K t.toMatrix (by rw [t.det]; exact isUnit_one)).prod := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, brp_coe_list_transvec, brp_coe_list_transvec, brpDiag_coe, hM]
    simp [Du]
  conv_lhs => rw [hg]
  rw [map_mul, map_mul, glChar_list_transvec, glChar_list_transvec, one_mul, mul_one, glChar_diag_pow K χ N hs, hdet]
  simp [Du]

end Char

section Single

variable (K : Type) [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem rowAct_scalar (t : K) :
    Formalism.GradedWeylDivisibility.rowAct K (r := n) (n := n) ((t • 1 : Matrix (Fin n) (Fin n) K))ᵀ = aeval fun v => C t * X v := by
  unfold Formalism.GradedWeylDivisibility.rowAct
  congr 1
  funext v
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply]
    intro h; exact absurd h hb
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rowAct_one_tr (F : MvPolynomial (Fin n × Fin n) K) :
    Formalism.GradedWeylDivisibility.rowAct K (r := n) (n := n) ((1 : Matrix (Fin n) (Fin n) K))ᵀ F = F := by
  have h := rowAct_scalar (n := n) K 1
  rw [one_smul] at h
  rw [h]
  simp

theorem trAct_single_scalar (lam : ι → DomWeight n) (τ : ι) (t : Kˣ) (F : Pol K ι n) (hF : F ∈ VV K lam) :
    trAct (Pi.mulSingle τ (brpSc K t)) F = (t : K) ^ (∑ i, (lam τ).natW i) • F := by
  unfold trAct
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨G, hG, rfl⟩ := hP
    rw [map_prod]
    have hfac : ∀ s, Formalism.GradedWeylDivisibility.blockAct K (fun σ => (((Pi.mulSingle τ (brpSc K t) : ι → GL (Fin n) K) σ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)ᵀ) (Formalism.GradedWeylDivisibility.blockEmb K s (G s)) =
        (if s = τ then (t : K) ^ (∑ i, (lam τ).natW i) else 1) • Formalism.GradedWeylDivisibility.blockEmb K s (G s) := by
      intro s
      rw [(Formalism.GradedWeylDivisibility.blockActTensor K K ι n n _).1 s (G s)]
      by_cases hs : s = τ
      · subst hs
        rw [if_pos rfl, Pi.mulSingle_eq_same, brpSc_coe, rowAct_scalar]
        have hW : G s ∈ weightedHomogeneousSubmodule K (Formalism.GradedWeylDivisibility.colW n n) (lam s).natW :=
          (Submodule.mem_inf.1 (hG s)).1
        rw [brp_aeval_scale_whom _ _ hW, map_smul]
      · rw [if_neg hs, Pi.mulSingle_eq_of_ne hs, Units.val_one, rowAct_one_tr, one_smul]
    rw [Finset.prod_congr rfl fun s _ => hfac s, Finset.prod_smul, Finset.prod_ite_eq' Finset.univ τ, if_pos (Finset.mem_univ τ)]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

theorem detTwK_single_scalar (lam : ι → DomWeight n) (τ : ι) (t : Kˣ) :
    detTwK lam (Pi.mulSingle τ (brpSc K t)) = (t : K) ^ ((n : ℤ) * (lam τ).detShift) := by
  unfold detTwK
  rw [Finset.prod_eq_single τ]
  · rw [Pi.mulSingle_eq_same]
    unfold detPow
    have hdet : (Matrix.GeneralLinearGroup.det (brpSc K t : GL (Fin n) K) : K) = (t : K) ^ n := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, brpSc_coe]
      simp
    rw [Units.val_zpow_eq_zpow_val, hdet, ← zpow_natCast, ← zpow_mul]
  · intro s _ hs
    rw [Pi.mulSingle_eq_of_ne hs]
    simp [detPow]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rhoK_single_scalar (lam : ι → DomWeight n) (τ : ι) (t : Kˣ) :
    rhoK lam (Pi.mulSingle τ (brpSc K t)) = ((t : K) ^ wsum (lam τ)) • (1 : Module.End K (VV K lam)) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  show actP lam (Pi.mulSingle τ (brpSc K t)) F.1 = ((t : K) ^ wsum (lam τ)) • F.1
  unfold actP
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, trAct_single_scalar K lam τ t F.1 F.2, detTwK_single_scalar, smul_smul]
  congr 1
  have ht : (t : K) ≠ 0 := t.ne_zero
  rw [wsum, brp_wsum, ← zpow_natCast, ← zpow_add₀ ht]
  congr 1
  push_cast
  ring

def chiAt (lam : ι → DomWeight n) (τ : ι) : GL (Fin n) K →* K :=
  (LinearMap.det : Module.End K (VV K lam) →* K).comp
    ((rhoK lam).comp (MonoidHom.mulSingle (fun _ : ι => GL (Fin n) K) τ))

theorem chiAt_scalar (lam : ι → DomWeight n) (τ : ι) (t : Kˣ) :
    chiAt K lam τ (brpSc K t) = (t : K) ^ (wsum (lam τ) * (Module.finrank K (VV K lam) : ℤ)) := by
  show LinearMap.det (rhoK lam (Pi.mulSingle τ (brpSc K t))) = _
  rw [rhoK_single_scalar, LinearMap.det_smul, map_one, mul_one, ← zpow_natCast, ← zpow_mul]

theorem detAll_pow [CharZero K] (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) :
    LinearMap.det (rhoK lam g) ^ n =
      ∏ τ, ((g τ : Matrix (Fin n) (Fin n) K).det) ^ (wsum (lam τ) * (Module.finrank K (VV K lam) : ℤ)) := by
  have h1 : LinearMap.det (rhoK lam g) = ∏ τ, chiAt K lam τ (g τ) := by
    have h0 := Finset.map_noncommProd Finset.univ (fun i => Pi.mulSingle i (g i))
      (fun i _ j _ _ => Pi.mulSingle_apply_commute g i j) ((LinearMap.det : Module.End K (VV K lam) →* K).comp (rhoK lam))
    rw [Finset.noncommProd_mulSingle g, Finset.noncommProd_eq_prod] at h0
    exact h0
  rw [h1, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun τ _ => glChar_pow K (chiAt K lam τ) _ (chiAt_scalar K lam τ) (g τ)

end Single

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.PFrames
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem isLattice_between {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (A B : Submodule (𝓞 E) W) (hA : Submodule.IsLattice E A) (hAB : A ≤ B) (T : ℕ) (hT : T ≠ 0)
    (hTB : ∀ x ∈ B, (T : E) • x ∈ A) : Submodule.IsLattice E B := by
  let f : W →ₗ[𝓞 E] W := ((T : ℕ) : 𝓞 E) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ((T : ℕ) : E) • x = ((T : ℕ) : E) • y := by
      simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using hxy
    exact smul_right_injective W (by exact_mod_cast hT : ((T : ℕ) : E) ≠ 0) h1
  have hmap : B.map f ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hTB x hx
    simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using h1
  haveI : IsNoetherian (𝓞 E) A := isNoetherian_of_fg_of_noetherian A hA.fg
  have hmfg : (B.map f).FG := by
    have h1 := IsNoetherian.noetherian ((B.map f).comap A.subtype)
    have h2 := h1.map A.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hmap] at h2
  exact ⟨Submodule.fg_of_fg_map_injective f hf hmfg,
    eq_top_iff.2 (le_trans (le_of_eq hA.span_eq_top.symm) (Submodule.span_mono (SetLike.coe_subset_coe.2 hAB)))⟩

theorem T_smul_of_disc {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (L D : Submodule (𝓞 E) W) (T : ℕ)
    (e : Nonempty ((D ⧸ L.comap D.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {((T : ℕ) : 𝓞 E)}))) :
    ∀ x ∈ D, (T : E) • x ∈ L := by
  have hk : ∀ z : 𝓞 E ⧸ Ideal.span {((T : ℕ) : 𝓞 E)}, ((T : ℕ) : 𝓞 E) • z = 0 := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H y =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton'.2 ⟨y, by rw [smul_eq_mul, mul_comm]⟩
  intro x hx
  obtain ⟨e⟩ := e
  have h1 : ((T : ℕ) : 𝓞 E) • (Submodule.Quotient.mk (⟨x, hx⟩ : D) : D ⧸ L.comap D.subtype) = 0 :=
    e.injective (by rw [map_smul, map_zero, hk])
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
  have h2 : ((T : ℕ) : E) • x = D.subtype (((T : ℕ) : 𝓞 E) • (⟨x, hx⟩ : D)) := by
    simp only [Submodule.subtype_apply, Submodule.coe_smul]
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h2]
  exact h1

end Gen

open Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem M_ne_zero (D : D7) (u : D.what₂.Word) : Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1 ≠ 0 := by
  have h1 := (D.mem u).A.T_prime.ne_zero
  have h2 := (D.host.g_prime 0).ne_zero
  have h3 := (D.host.g_prime 1).ne_zero
  unfold Formalism.MainNotions.flipTwoThree.Tu
  positivity

theorem framesStep_of_gen {D : D7} (X : FullTied D) (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m)
    (hgen : GenMod (dualL D.sp.cm (D.sp.X i) (X.base.lev u i h1 hm).Lb)
      (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1)) : FramesStep D u i := by
  set lev := X.base.lev u i h1 hm
  have hT0 : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have hLb : Submodule.IsLattice D.host.E lev.Lb := ⟨Module.Finite.iff_fg.1 lev.Lb_fin, lev.Lb_span⟩
  have hLbd : IsLat (dualL D.sp.cm (D.sp.X i) lev.Lb) := by
    have := isLattice_between lev.Lb _ hLb lev.Lb_int _ hT0 lev.Lb_dual
    exact ⟨Module.Finite.iff_fg.2 this.fg, this.span_eq_top⟩
  have hΔ : ∀ c, Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c)) := by
    intro c
    refine isLattice_between _ _ (D.clsLat_lat u i c) ?_ _ hT0
      (T_smul_of_disc _ _ _ ((X.atT u).disc i hm c))
    intro x hx
    have := clsLat_int X u i hm c x hx
    rw [dualSub_eq] at this
    exact this
  obtain ⟨e, he, hsep⟩ := frames_of_tie (X.base.cls u i h1 hm) hLbd hΔ _ (M_ne_zero D u) hgen
    (fun k hkU hst hcg => stepLevel_mem lev k hkU hst hcg)
  have hr : (D.sp.X i).rank = D.R.N i := D.sp.X_rank i hm
  refine ⟨fun c a => e c (Fin.cast hr.symm a), fun c a => he c _, fun c c' h => hsep c c' ?_⟩
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := h
  refine ⟨γ, hγ1, hγ2, fun a => ?_⟩
  have := hγ3 (Fin.cast hr a)
  simpa using this

theorem framesP_of_gen {D : D7} (X : FullTied D) (u : D.what₂.Word)
    (hgen : GenMod (crdLat D.sp.X' D.sp.X'.L0) (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1)) : FramesP X u := by
  have hsd := coordinate_lattice_self_dual D.sp.cm D.sp.X'
  have hLbd : IsLat (dualL D.sp.cm D.sp.X' (crdLat D.sp.X' D.sp.X'.L0)) := by
    rw [hsd]; exact Fr.isLat_crd _ _ D.sp.X'.standardTuple_isLattice
  have hΔ : ∀ c, Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.dual D.sp.X'.hT ((X.atT u).lattice₂ c)) := by
    intro c
    have h := localLattice_selfDual X u c
    have hle : Formalism.HermitianLatticesTheory.dual D.sp.X'.hT ((X.atT u).lattice₂ c) ≤ (X.atT u).lattice₂ c := by
      have h2 := h.2.2
      rw [dualSub_eq] at h2
      have h3 := AddSubgroup.relIndex_eq_one.1 h2
      intro x hx
      exact h3 hx
    have hge : (X.atT u).lattice₂ c ≤ Formalism.HermitianLatticesTheory.dual D.sp.X'.hT ((X.atT u).lattice₂ c) := by
      intro x hx
      have := h.2.1 x hx
      rw [dualSub_eq] at this
      exact this
    rw [le_antisymm hle hge]
    exact h.1
  rw [← hsd] at hgen
  obtain ⟨e, he, hsep⟩ := frames_of_tie (X.atT u).clsP hLbd hΔ _ (M_ne_zero D u) hgen
    (fun k hkU hst hcg => stepLevel0_mem hsd (X.atT u).levP _ k hkU hst hcg)
  have hr : D.sp.X'.rank = D.R.N D.R.m - 1 := by
    rw [D.sp.X'_rank, factXm D.R]; omega
  refine ⟨fun c a => e c (Fin.cast hr.symm a), fun c a => he c _, fun c c' h => hsep c c' ?_⟩
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := h
  refine ⟨γ, hγ1, hγ2, fun a => ?_⟩
  have := hγ3 (Fin.cast hr a)
  simpa using this

theorem framesStep_pos {D : D7} (X : FullTied D) (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) :
    FramesStep D u i := by
  refine framesStep_of_gen X u i h1 hm (genMod _ (M_ne_zero D u) _ ?_)
  set lev := X.base.lev u i h1 hm
  have hLb : Submodule.IsLattice D.host.E lev.Lb := ⟨Module.Finite.iff_fg.1 lev.Lb_fin, lev.Lb_span⟩
  exact Module.Finite.iff_fg.2
    (isLattice_between lev.Lb _ hLb lev.Lb_int _ (D.mem u).A.T_prime.ne_zero lev.Lb_dual).fg

theorem frames_of_classes {D : D7} (X : FullTied D) (u : D.what₂.Word) : FramesP X u :=
  framesP_of_gen X u (genMod _ (M_ne_zero D u) _ (Fr.isLat_crd _ _ D.sp.X'.standardTuple_isLattice).1)

theorem ClsTieOfTied_of_step0 (h0 : ∀ (D : D7), FullTied D → ∀ u, FramesStep D u 0) : ClassCompatibilityOfRowCompatibility := by
  refine ClsTieOfTied_of_frames (fun D X u i hi => ?_) (fun D X u => frames_of_classes X u)
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · exact h0 D X u
  · exact framesStep_pos X u i h1 hi

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.PMsGram
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Gram

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def meanAbs (z : E) : ℝ := (∑ φ : E →+* ℂ, ‖φ z‖) / (Module.finrank ℚ E : ℝ)

def ShortFrame (S : HSpace E) (q : ℕ) (ρ : ℝ) : Prop :=
  ∀ L : Submodule (𝓞 E) S.V, Submodule.IsLattice E L → LatT S q L →
    ∃ b : Module.Basis (Fin S.rank) E S.V, (∀ c, b c ∈ L) ∧ ∀ c, meanAbs (S.hT (b c) (b c)) ≤ ρ

def CSAt (S : HSpace E) : Prop :=
  ∀ (φ : E →+* ℂ) (x y : S.V), ‖φ (S.hT x y)‖ ^ 2 ≤ ‖φ (S.hT x x)‖ * ‖φ (S.hT y y)‖

def CoordCount (S : HSpace E) (q : ℕ) (ρ B2 : ℝ) : Prop :=
  ∃ C : Matrix (Fin S.rank) (Fin S.rank) E → Finset (Submodule (𝓞 E) (Fin S.rank → E)),
    (∀ G, ((C G).card : ℝ) ≤ Real.exp B2) ∧
    ∀ (L : Submodule (𝓞 E) S.V) (b : Module.Basis (Fin S.rank) E S.V), Submodule.IsLattice E L → LatT S q L →
      (∀ c, b c ∈ L) → (∀ c, meanAbs (S.hT (b c) (b c)) ≤ ρ) → (keyOf S b L).2 ∈ C (keyOf S b L).1

theorem meanAbs_entry (S : HSpace E) (hCS : CSAt S) {ρ : ℝ} {x y : S.V} (hx : meanAbs (S.hT x x) ≤ ρ)
    (hy : meanAbs (S.hT y y) ≤ ρ) : meanAbs (S.hT x y) ≤ ρ := by
  have hpt : ∀ φ : E →+* ℂ, ‖φ (S.hT x y)‖ ≤ (‖φ (S.hT x x)‖ + ‖φ (S.hT y y)‖) / 2 := by
    intro φ
    have h := hCS φ x y
    nlinarith [sq_nonneg (‖φ (S.hT x x)‖ - ‖φ (S.hT y y)‖), norm_nonneg (φ (S.hT x y)),
      norm_nonneg (φ (S.hT x x)), norm_nonneg (φ (S.hT y y))]
  unfold meanAbs at *
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  rw [div_le_iff₀ hd] at hx hy ⊢
  have hs := Finset.sum_le_sum fun φ (_ : φ ∈ (Finset.univ : Finset (E →+* ℂ))) => hpt φ
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hs
  linarith

theorem keyBound_of (S : HSpace E) (q : ℕ) (ρ B2 : ℝ) (hρ : 0 ≤ ρ) (hB2 : 0 ≤ B2)
    (hS : ShortFrame S q ρ) (hCS : CSAt S) (hC : CoordCount S q ρ B2) :
    KeyBound S q ((S.rank : ℝ) ^ 2 * (Module.finrank ℚ E : ℝ) * Real.log (2 * ρ + 1) + B2) := by
  classical
  obtain ⟨hfin, hcard⟩ := Formalism.HermitianLattices.ExplicitEstimates.mean_count_of_moduli_space E ρ hρ
  obtain ⟨C, hCc, hCm⟩ := hC
  set Z : Finset E := hfin.toFinset.image (fun x : 𝓞 E => (x : E)) with hZ
  have hZc : (Z.card : ℝ) ≤ (2 * ρ + 1) ^ Module.finrank ℚ E := by
    refine le_trans ?_ hcard
    have : Z.card ≤ hfin.toFinset.card := Finset.card_image_le
    rw [← Set.ncard_eq_toFinset_card _ hfin] at this
    exact_mod_cast this
  let G : Finset (Matrix (Fin S.rank) (Fin S.rank) E) := Fintype.piFinset fun _ => Fintype.piFinset fun _ => Z
  have hGc : (G.card : ℝ) ≤ ((2 * ρ + 1) ^ Module.finrank ℚ E) ^ (S.rank * S.rank) := by
    have : G.card = (Z.card ^ S.rank) ^ S.rank := by
      show (Fintype.piFinset fun _ => Fintype.piFinset fun _ => Z : Finset (Fin S.rank → Fin S.rank → E)).card = _
      rw [Fintype.card_piFinset]
      simp [Fintype.card_piFinset, Finset.prod_const]
    rw [this, pow_mul]
    push_cast
    exact pow_le_pow_left₀ (pow_nonneg (by positivity) _) (pow_le_pow_left₀ (by positivity) hZc S.rank) S.rank
  let K := G.biUnion fun g => (C g).image fun c => (g, c)
  refine ⟨K, ?_, fun L hL hq => ?_⟩
  · have hK : (K.card : ℝ) ≤ G.card * Real.exp B2 := by
      have h1 : K.card ≤ ∑ g ∈ G, ((C g).image fun c => (g, c)).card := Finset.card_biUnion_le
      have h3 : K.card ≤ ∑ g ∈ G, (C g).card := h1.trans (Finset.sum_le_sum fun g _ => Finset.card_image_le)
      have h2 : (K.card : ℝ) ≤ ∑ g ∈ G, ((C g).card : ℝ) := by exact_mod_cast h3
      refine le_trans h2 ?_
      refine le_trans (Finset.sum_le_sum fun g _ => hCc g) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have hlog : 0 ≤ Real.log (2 * ρ + 1) := Real.log_nonneg (by linarith)
    rcases Nat.eq_zero_or_pos K.card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; positivity
    have hGpos : (0 : ℝ) < G.card := by
      have : (0 : ℝ) < G.card * Real.exp B2 := lt_of_lt_of_le (by exact_mod_cast h0) hK
      exact pos_of_mul_pos_left this (Real.exp_pos _).le
    calc Real.log K.card ≤ Real.log (G.card * Real.exp B2) := Real.log_le_log (by exact_mod_cast h0) hK
      _ = Real.log G.card + B2 := by rw [Real.log_mul hGpos.ne' (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ Real.log (((2 * ρ + 1) ^ Module.finrank ℚ E) ^ (S.rank * S.rank)) + B2 := by
          gcongr
      _ = (S.rank : ℝ) ^ 2 * (Module.finrank ℚ E : ℝ) * Real.log (2 * ρ + 1) + B2 := by
          rw [Real.log_pow, Real.log_pow]; push_cast; ring
  · obtain ⟨b, hbL, hbs⟩ := hS L hL hq
    refine ⟨b, Finset.mem_biUnion.2 ⟨(keyOf S b L).1, ?_, Finset.mem_image.2 ⟨(keyOf S b L).2,
      hCm L b hL hq hbL hbs, rfl⟩⟩⟩
    have key : ∀ i j, (keyOf S b L).1 i j ∈ Z := by
      intro i j
      have hmem := (mem_dualSub S L (b j)).1 (hq.1 _ (hbL j)) (b i) (hbL i)
      obtain ⟨z, hz⟩ := hmem
      have hzm : z ∈ hfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        show meanAbs (z : E) ≤ ρ
        have : (z : E) = S.hT (b i) (b j) := hz
        rw [this]
        exact meanAbs_entry S hCS (hbs i) (hbs j)
      exact Finset.mem_image.2 ⟨z, hzm, hz⟩
    exact Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun j => key i j

end Gram

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

