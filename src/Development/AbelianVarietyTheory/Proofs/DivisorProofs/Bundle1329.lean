import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Formalism.HarderNarasimhan.StatementPl
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimTranslationInvariant
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TransODE

open NormedSpace

theorem linear_ode_eq_exp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (y : ℝ → E) (hy : ∀ s, HasDerivAt y (L (y s)) s) (t : ℝ) :
    y t = exp (t • L) (y 0) := by
  let z : ℝ → E := fun s => exp ((t - s) • L) (y s)
  have hd : ∀ s, HasDerivAt z 0 s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => exp (u • L)) (exp ((t - s) • L) * L) (t - s) :=
      hasDerivAt_exp_smul_const L (t - s)
    have h2 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have h3 := h1.scomp s h2
    have h4 := h3.clm_apply (hy s)
    convert h4 using 1
    · rfl
    · simp [Function.comp_def]
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [z] using hc

theorem mem_of_translate (G : Type) [Group G] (W : Submodule ℂ (G → ℂ)) (γ : ℝ → G)
    (hfin : FiniteDimensional ℂ W) (hγ : γ 0 = 1)
    (hder : ∀ ψ ∈ W, ∃ ψ' ∈ W, ∀ (g : G) (t : ℝ),
      HasDerivAt (fun τ : ℝ => ψ (γ τ * g)) (ψ' (γ t * g)) t) :
    ∀ ψ ∈ W, ∀ t : ℝ, (fun g => ψ (γ t * g)) ∈ W := by
  classical
  let d := Module.finrank ℂ W
  let b : Module.Basis (Fin d) ℂ W := Module.finBasis ℂ W
  have hb : ∀ i, ∃ ψ' ∈ W, ∀ (g : G) (t : ℝ),
      HasDerivAt (fun τ : ℝ => (b i : G → ℂ) (γ τ * g)) (ψ' (γ t * g)) t :=
    fun i => hder _ (b i).2
  choose D hDW hD using hb
  have hexp : ∀ (w : W) (x : G), (w : G → ℂ) x = ∑ j, b.repr w j * (b j : G → ℂ) x := by
    intro w x
    calc (w : G → ℂ) x = ((∑ j, b.repr w j • b j : W) : G → ℂ) x := by rw [b.sum_repr w]
      _ = _ := by
        rw [Submodule.coe_sum]
        simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  let M : Matrix (Fin d) (Fin d) ℂ := fun i j => b.repr ⟨D i, hDW i⟩ j
  have hM : ∀ i x, D i x = ∑ j, M i j * (b j : G → ℂ) x := fun i x => hexp ⟨D i, hDW i⟩ x
  let Lc : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
  let L : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) := Lc.restrictScalars ℝ
  have hL : ∀ v i, L v i = ∑ j, M i j * v j := by
    intro v i; simp [L, Lc, Matrix.mulVec, dotProduct]
  have hLc : ∀ (c : ℂ) v, L (c • v) = c • L v := fun c v => by simp [L]
  have hLs : ∀ (f : Fin d → (Fin d → ℂ)), L (∑ j, f j) = ∑ j, L (f j) := fun f => map_sum L f _
  have key : ∀ (g : G) (t : ℝ) i, (b i : G → ℂ) (γ t * g) =
      ∑ j, (exp (t • L) (Pi.single j 1)) i * (b j : G → ℂ) g := by
    intro g t i
    let y : ℝ → (Fin d → ℂ) := fun s k => (b k : G → ℂ) (γ s * g)
    have hy : ∀ s, HasDerivAt y (L (y s)) s := by
      intro s
      rw [hasDerivAt_pi]
      intro k
      have := hD k g s
      rw [hM] at this
      simpa [y, hL] using this
    let v : Fin d → ℂ := fun j => (b j : G → ℂ) g
    let y2 : ℝ → (Fin d → ℂ) := fun s => ∑ j, v j • exp (s • L) (Pi.single j 1)
    have hy2 : ∀ s, HasDerivAt y2 (L (y2 s)) s := by
      intro s
      have : HasDerivAt y2 (∑ j, v j • (L * exp (s • L)) (Pi.single j 1)) s := by
        have := HasDerivAt.fun_sum (u := Finset.univ) (A := fun j s => v j • exp (s • L) (Pi.single j 1))
          (A' := fun j => v j • (L * exp (s • L)) (Pi.single j 1)) (x := s) (fun j _ =>
            (((hasDerivAt_exp_smul_const' L s).clm_apply (hasDerivAt_const s (Pi.single j (1:ℂ) : Fin d → ℂ))).const_smul (v j)).congr_deriv (by simp))
        simpa [y2] using this
      convert this using 1
      simp [y2, hLs, hLc, ContinuousLinearMap.mul_apply]
    have e1 := GlobalTheory.TransODE.linear_ode_eq_exp L y hy t
    have e2 := GlobalTheory.TransODE.linear_ode_eq_exp L y2 hy2 t
    have h0 : y 0 = y2 0 := by
      funext k
      simp [y, y2, v, hγ, Pi.single_apply]
    have := congrFun (e1.trans (h0 ▸ e2.symm)) i
    simpa [y, y2, v, mul_comm, Finset.sum_apply] using this
  intro ψ hψ t
  have hfun : (fun g => ψ (γ t * g)) = ∑ i, b.repr ⟨ψ, hψ⟩ i •
      ∑ j, (exp (t • L) (Pi.single j 1)) i • (b j : G → ℂ) := by
    funext g
    have := hexp ⟨ψ, hψ⟩ (γ t * g)
    simp only at this
    rw [this]
    simp [key, Finset.sum_apply, Finset.mul_sum]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2)

theorem main : ∀ (G : Type) [Group G] (W : Submodule ℂ (G → ℂ)) (γ : ℝ → G), FiniteDimensional ℂ W → γ 0 = 1 → (∀ ψ ∈ W, ∃ ψ' ∈ W, ∀ (g : G) (t : ℝ), HasDerivAt (fun τ : ℝ => ψ (γ τ * g)) (ψ' (γ t * g)) t) → ∀ ψ ∈ W, ∀ t : ℝ, (fun g => ψ (γ t * g)) ∈ W :=
  fun G _ W γ hfin hγ hder => mem_of_translate G W γ hfin hγ hder

end GlobalTheory.TransODE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteParabolicDoubleCosetsOrbitalIntegral
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LeviDesc.OrbFin
open GlobalTheory.LeviDesc.Krylov

theorem exists_cyclic {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (hy : y.charpoly.Separable) :
    ∃ e : Fin r → F, IsUnit (krylov y e).det :=
  GlobalTheory.T.exists_isUnit_det_krylovMatrix_of_separable y hy

theorem krylov_conj_eq {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F) (e e' : Fin r → F)
    (hc : y.charpoly = y'.charpoly) (he : IsUnit (krylov y e).det) (he' : IsUnit (krylov y' e').det) :
    (krylov y e)⁻¹ * y * krylov y e = (krylov y' e')⁻¹ * y' * krylov y' e' :=
  GlobalTheory.T.krylovMatrix_conj_eq_of_charpoly_eq y y' e e' hc he he'

theorem isClosed_charpoly_eq (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ)
    (χ : (w.adicCompletion E)[X]) : IsClosed {y : GLw r w | y.val.charpoly = χ} := by
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  haveI : Infinite (w.adicCompletion E) := Infinite.of_injective Nat.cast Nat.cast_injective
  have hset : {y : GLw r w | y.val.charpoly = χ} =
      ⋂ t : w.adicCompletion E, {y : GLw r w | ((Matrix.scalar (Fin r) t) - y.val).det = χ.eval t} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hy t; rw [← Matrix.eval_charpoly, hy]
    · intro hy; exact Polynomial.funext fun t => by rw [Matrix.eval_charpoly]; exact hy t
  rw [hset]
  refine isClosed_iInter fun t => isClosed_eq ?_ continuous_const
  exact (continuous_const.sub Units.continuous_val).matrix_det

theorem exists_compact_krylov (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (Ω : Set (GLw r w))
    (hΩ : IsCompact Ω) (h : ∀ y ∈ Ω, ∃ e, IsUnit (krylov y.val e).det) :
    ∃ C : Set (GLw r w), IsCompact C ∧ ∀ y ∈ Ω, ∃ e, ∃ c ∈ C, c.val = krylov y.val e :=
  GlobalTheory.T.exists_compact_invertible_krylovMatrices E w r Ω hΩ h

theorem isOpen_KGL (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) :
    IsOpen (GlobalTheory.LFun.KGL w r : Set (GLw r w)) :=
  GlobalTheory.LFun.IntPtsUnitary.isOpen_GLint _ (Valued.isOpen_integer (w.adicCompletion E))

theorem orbit_fin (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (γ : GLw r w)
    (hs : γ.val.charpoly.Separable) (Ω : Set (GLw r w)) (hΩ : IsCompact Ω) :
    ∃ T : Set (GLw r w), T.Finite ∧ ∀ q : GLw r w, q⁻¹ * γ * q ∈ Ω →
      ∃ z : GLw r w, z * γ = γ * z ∧ ∃ t ∈ T, ∃ k ∈ GlobalTheory.LFun.KGL w r, q = z * t * k := by
  set Ωχ := Ω ∩ {y : GLw r w | y.val.charpoly = γ.val.charpoly} with hΩχ
  have hcpt : IsCompact Ωχ := hΩ.inter_right (isClosed_charpoly_eq E w r _)
  have hcyc : ∀ y ∈ Ωχ, ∃ e, IsUnit (krylov y.val e).det := fun y hy =>
    exists_cyclic _ (by rw [hy.2]; exact hs)
  obtain ⟨C, hC, hCy⟩ := exists_compact_krylov E w r Ωχ hcpt hcyc
  obtain ⟨f, hf⟩ := exists_cyclic γ.val hs
  have hfu : IsUnit (krylov γ.val f) := (Matrix.isUnit_iff_isUnit_det _).2 hf
  set Bf : GLw r w := hfu.unit with hBf
  set D : Set (GLw r w) := (fun c => Bf * c⁻¹) '' C with hD
  have hDc : IsCompact D := hC.image (continuous_const.mul continuous_inv)
  have hKo := isOpen_KGL E w r
  obtain ⟨T, hT⟩ := hDc.elim_finite_subcover (fun c : GLw r w => (fun x => c⁻¹ * x) ⁻¹' (GlobalTheory.LFun.KGL w r : Set (GLw r w)))
    (fun c => hKo.preimage (continuous_const.mul continuous_id)) (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine ⟨(T : Set (GLw r w)), T.finite_toSet, fun q hq => ?_⟩
  have hy : q⁻¹ * γ * q ∈ Ωχ := by
    refine ⟨hq, ?_⟩
    show ((q⁻¹ * γ * q : GLw r w) : Matrix (Fin r) (Fin r) (w.adicCompletion E)).charpoly = γ.val.charpoly
    have := Matrix.charpoly_units_conj (q⁻¹) γ.val
    simpa [Matrix.coe_units_inv] using this
  obtain ⟨e, c, hcC, hce⟩ := hCy _ hy
  have he : IsUnit (krylov (q⁻¹ * γ * q : GLw r w).val e).det := by
    rw [← hce, ← Matrix.isUnit_iff_isUnit_det]; exact c.isUnit
  have hconj := krylov_conj_eq _ _ e f (hy.2) he hf
  have h1 : c⁻¹ * (q⁻¹ * γ * q) * c = Bf⁻¹ * γ * Bf := by
    ext1
    rw [Units.val_mul (c⁻¹ * (q⁻¹ * γ * q)) c, Units.val_mul c⁻¹ (q⁻¹ * γ * q), Units.val_mul (Bf⁻¹ * γ) Bf,
      Units.val_mul Bf⁻¹ γ, Matrix.coe_units_inv c, Matrix.coe_units_inv Bf, hce, hBf, IsUnit.unit_spec]
    exact hconj
  have hxD : Bf * c⁻¹ ∈ D := ⟨c, hcC, rfl⟩
  obtain ⟨t, htT, ht⟩ := Set.mem_iUnion₂.1 (hT hxD)
  refine ⟨q * c * Bf⁻¹, ?_, t, htT, t⁻¹ * (Bf * c⁻¹), ht, by group⟩
  calc q * c * Bf⁻¹ * γ = q * c * (Bf⁻¹ * γ * Bf) * Bf⁻¹ := by group
    _ = q * c * (c⁻¹ * (q⁻¹ * γ * q) * c) * Bf⁻¹ := by rw [h1]
    _ = γ * (q * c * Bf⁻¹) := by group

theorem avg_ne_zero_exists {H : Type} [Group H] (u : H → ℂ) (h : avg u ≠ 0) : ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  simp [avg, hc]

theorem charpoly_blk_separable (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (hs : (m.1.val.charpoly * m.2.val.charpoly).Separable) :
    (blk h w m 0 : GLw n w).val.charpoly.Separable := by
  have hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  have hval : ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val) := by
    simp only [blk]
    rw [dif_pos hM]
    rfl
  rw [hval, Matrix.charpoly_reindex, Matrix.mul_zero, Matrix.charpoly_fromBlocks_zero₁₂]
  exact hs

theorem fin_doubleCosets : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, {d : DoubleCoset.Quotient (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) : Set (GlobalTheory.LeviDesc.parP a n w)) (((GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w) : Subgroup _) : Set (GlobalTheory.LeviDesc.parP a n w)) | GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (((Quotient.out d)⁻¹ * ⟨blk h w m 0, hγ⟩ * Quotient.out d : GlobalTheory.LeviDesc.parP a n w) : GLw n w) ≠ 0}.Finite := by
  intro E _ _ n a b h w f hf m hs hγ
  obtain ⟨K', -, hsupp, -⟩ := hf
  set γ : GLw n w := blk h w m 0 with hγdef
  set P := GlobalTheory.LeviDesc.parP a n w
  set K := GlobalTheory.LFun.KGL w n
  set γP : P := ⟨γ, hγ⟩
  obtain ⟨T, hT, hTq⟩ := orbit_fin E w n γ (charpoly_blk_separable E n a b h w m hs) (tsupport f) hsupp
  have hcent : ∀ z : GLw n w, z * γ = γ * z → z ∈ P := fun z hz =>
    GlobalTheory.LeviDesc.twCent_blk_le_parP E n a b h w m hs (show z * γ = γ * MonoidHom.id _ z from hz)
  let Q : DoubleCoset.Quotient (twCent (MonoidHom.id _) γP : Set P) ((K.subgroupOf P : Subgroup P) : Set P) → GLw n w → Prop :=
    fun d t => t ∈ T ∧ ∃ z : GLw n w, z * γ = γ * z ∧ ∃ k ∈ K, ((Quotient.out d : P) : GLw n w) = z * t * k
  have hex : ∀ d ∈ {d : DoubleCoset.Quotient (twCent (MonoidHom.id _) γP : Set P) ((K.subgroupOf P : Subgroup P) : Set P) |
      GlobalTheory.LeviDesc.cavg K f (((Quotient.out d)⁻¹ * γP * Quotient.out d : P) : GLw n w) ≠ 0}, ∃ t, Q d t := by
    intro d hd
    obtain ⟨k, hk⟩ := avg_ne_zero_exists _ hd
    set p : GLw n w := ((Quotient.out d : P) : GLw n w)
    have hmem : (p * k)⁻¹ * γ * (p * k) ∈ tsupport f := by
      apply subset_tsupport
      have : (p * k)⁻¹ * γ * (p * k) = (k : GLw n w)⁻¹ * (((Quotient.out d)⁻¹ * γP * Quotient.out d : P) : GLw n w) * k := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, p, γP]; group
      rw [this]; exact hk
    obtain ⟨z, hz, t, ht, k₁, hk₁, hq⟩ := hTq _ hmem
    refine ⟨t, ht, z, hz, k₁ * (k : GLw n w)⁻¹, K.mul_mem hk₁ (K.inv_mem k.2), ?_⟩
    rw [← mul_assoc, ← hq, mul_inv_cancel_right]
  refine Set.Finite.of_injOn (f := fun d => if hd : ∃ t, Q d t then hd.choose else 1) (t := T) ?_ ?_ hT
  · intro d hd
    simp only [dif_pos (hex d hd)]
    exact (hex d hd).choose_spec.1
  · intro d₁ hd₁ d₂ hd₂ heq
    simp only [dif_pos (hex d₁ hd₁), dif_pos (hex d₂ hd₂)] at heq
    obtain ⟨-, z₁, hz₁, k₁, hk₁, hp₁⟩ := (hex d₁ hd₁).choose_spec
    obtain ⟨-, z₂, hz₂, k₂, hk₂, hp₂⟩ := (hex d₂ hd₂).choose_spec
    rw [heq] at hp₁
    set t := (hex d₂ hd₂).choose
    have hzP : z₂ * z₁⁻¹ ∈ P := hcent _ (by
      calc z₂ * z₁⁻¹ * γ = z₂ * (z₁⁻¹ * (γ * z₁)) * z₁⁻¹ := by group
        _ = z₂ * (z₁⁻¹ * (z₁ * γ)) * z₁⁻¹ := by rw [hz₁]
        _ = (z₂ * γ) * z₁⁻¹ := by group
        _ = (γ * z₂) * z₁⁻¹ := by rw [hz₂]
        _ = γ * (z₂ * z₁⁻¹) := by group)
    set hP : P := ⟨z₂ * z₁⁻¹, hzP⟩
    have hcP : hP ∈ twCent (MonoidHom.id _) γP := by
      show hP * γP = γP * MonoidHom.id _ hP
      apply Subtype.ext
      simp only [Subgroup.coe_mul, MonoidHom.id_apply, hP, γP]
      calc z₂ * z₁⁻¹ * γ = z₂ * (z₁⁻¹ * (γ * z₁)) * z₁⁻¹ := by group
        _ = z₂ * (z₁⁻¹ * (z₁ * γ)) * z₁⁻¹ := by rw [hz₁]
        _ = (z₂ * γ) * z₁⁻¹ := by group
        _ = (γ * z₂) * z₁⁻¹ := by rw [hz₂]
        _ = γ * (z₂ * z₁⁻¹) := by group
    set kP : P := (Quotient.out d₁)⁻¹ * hP⁻¹ * Quotient.out d₂
    have hkv : (kP : GLw n w) = k₁⁻¹ * k₂ := by
      simp only [kP, hP, Subgroup.coe_mul, Subgroup.coe_inv, hp₁, hp₂]; group
    have hkK : kP ∈ K.subgroupOf P := by
      rw [Subgroup.mem_subgroupOf, hkv]; exact K.mul_mem (K.inv_mem hk₁) hk₂
    rw [← DoubleCoset.out_eq' _ _ d₁, ← DoubleCoset.out_eq' _ _ d₂, DoubleCoset.eq]
    exact ⟨hP, hcP, kP, hkK, by simp only [kP]; group⟩

end GlobalTheory.LeviDesc.OrbFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProductOfLocalFunctionsUnitaryNeZero
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.HSupp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_cLoc_val (hE : Unr E) (w : Pl E) (x : finU E n) :
    ((toSub (UL n w) (cLoc w (x : UA E n)) : UL n w) : GLw n w) = cLoc w (x : UA E n) := by
  unfold toSub
  rw [dif_pos (cLoc_mem_UL E hE n w x)]

theorem factor_ne_zero (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (hK : ∀ᶠ w in cofinite, K' w = KL n w)
    (f : ∀ w : Pl E, UL n w → ℂ) (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1)
    (x : finU E n) (hx : globFn S f x ≠ 0) :
    ∀ w ∈ S, f w (toSub (UL n w) (cLoc w (x : UA E n))) ≠ 0 := by
  set g : Pl E → ℂ := fun w => f w (toSub (UL n w) (cLoc w (x : UA E n))) with hg
  have hB : {w | ¬ (f w = (KL n w : Set (UL n w)).indicator 1 ∧
      toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w)}.Finite :=
    Filter.eventually_cofinite.1 (hf.and (RegVan.eventually_toSub_mem (n := n) x))
  have hfin : (S ∩ Function.mulSupport g).Finite := by
    refine hB.subset fun w hw => ?_
    intro hc
    apply hw.2
    change f w _ = 1
    rw [hc.1]
    exact Set.indicator_of_mem hc.2 _
  intro w hwS
  by_cases hm : w ∈ Function.mulSupport g
  · have hx' : ∏ᶠ w ∈ S, g w ≠ 0 := hx
    rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod _ hfin] at hx'
    exact Finset.prod_ne_zero_iff.1 hx' w (hfin.mem_toFinset.2 ⟨hwS, hm⟩)
  · rw [Function.notMem_mulSupport] at hm
    change g w ≠ 0
    rw [hm]
    exact one_ne_zero

end GlobalTheory.BCT.HSupp

open GlobalTheory.BCT.HSupp in

theorem GlobalTheory.BCT.finite_globFn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ)
    (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ,
    IsTest (KL n) K' f → {q : finU E n ⧸ globLev S K' | globFn S f q.out ≠ 0}.Finite := by
  intro E _ _ _ hE n S K' hK f hf
  set F : Set (Pl E) := {w | ¬ (K' w = KL n w ∧ f w = (KL n w : Set (UL n w)).indicator 1)} with hF
  have hFfin : F.Finite := Filter.eventually_cofinite.1 (hK.2.and hf.2)
  have key := factor_ne_zero S K' hK.2 f hf.2
  have inK : ∀ x : finU E n, globFn S f x ≠ 0 → ∀ w ∈ S, w ∉ F →
      toSub (UL n w) (cLoc w (x : UA E n)) ∈ K' w := by
    intro x hx w hwS hwF
    simp only [hF, Set.mem_setOf_eq, not_not] at hwF
    have h := key x hx w hwS
    rw [hwF.2] at h
    rw [hwF.1]
    by_contra hc
    exact h (Set.indicator_of_notMem hc _)
  haveI : Finite ↥(F ∩ S) := (hFfin.inter_of_left S).to_subtype
  let Φ : finU E n ⧸ globLev S K' → ∀ w : ↥(F ∩ S), UL n w.1 ⧸ K' w.1 := fun q w =>
    (toSub (UL n w.1) (cLoc w.1 (q.out : UA E n)) : UL n w.1 ⧸ K' w.1)
  refine Set.Finite.of_injOn (f := Φ)
    (t := Set.pi Set.univ fun w : ↥(F ∩ S) => {c : UL n w.1 ⧸ K' w.1 | f w.1 c.out ≠ 0}) ?_ ?_
    (Set.Finite.pi fun w => LevOpTmul.finite_supp (hK.1 w.1).1 (hf.1 w.1).1)
  · intro q hq w _
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K' w.1) (toSub (UL n w.1) (cLoc w.1 (q.out : UA E n)))
    change f w.1 (QuotientGroup.mk _ : UL n w.1 ⧸ K' w.1).out ≠ 0
    rw [hh, ((hf.1 w.1).2 h h.2 _).2]
    exact key _ hq w.1 w.2.2
  · intro q₁ hq₁ q₂ hq₂ he
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
    refine QuotientGroup.eq.2 ((mem_globLev_iff S K' _).2 fun w hwS => ?_)
    refine ⟨(toSub (UL n w) (cLoc w (q₁.out : UA E n)))⁻¹ * toSub (UL n w) (cLoc w (q₂.out : UA E n)), ?_, ?_⟩
    · by_cases hwF : w ∈ F
      · have := congrFun he ⟨w, hwF, hwS⟩
        exact QuotientGroup.eq.1 this
      · exact mul_mem (inv_mem (inK _ hq₁ w hwS hwF)) (inK _ hq₂ w hwS hwF)
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, toSub_cLoc_val hE, toSub_cLoc_val hE, Subgroup.coe_mul,
        Subgroup.coe_inv, map_mul, map_inv]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRationalPointsConjInSupport
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finite_support_conj_points : ∀ (G H : Type) [Group G] [Group H] (ι : H →* G), Function.Injective ι → ∀ (K' : Subgroup G) (F : G → ℂ), (∀ k ∈ K', ∀ x, F (x * k) = F x) → {q : G ⧸ K' | F q.out ≠ 0}.Finite → ∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G) → {h : H | F (x⁻¹ * ι h * x) ≠ 0}.Finite := by
  intro G H _ _ ι hι K' F hF hT x hfin
  have key : ∀ g : G, F ((g : G ⧸ K').out) = F g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K' g
    rw [hk]; exact hF _ k.2 g
  have hL : (ι ⁻¹' ((ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G)).Finite :=
    (Set.finite_coe_iff.mp hfin).preimage hι.injOn
  refine Set.Finite.of_finite_fibers (fun h : H => ((x⁻¹ * ι h * x : G) : G ⧸ K')) (hT.subset ?_) ?_
  · rintro _ ⟨h, hh, rfl⟩
    simp only [Set.mem_setOf_eq] at hh ⊢
    rwa [key]
  · rintro _ ⟨h0, -, rfl⟩
    refine (hL.image (fun k => h0 * k)).subset ?_
    rintro h ⟨-, hh⟩
    refine ⟨h0⁻¹ * h, ?_, by simp⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hh
    have hk : (x⁻¹ * ι h0 * x)⁻¹ * (x⁻¹ * ι h * x) ∈ K' := QuotientGroup.eq.mp hh.symm
    have hk' : x⁻¹ * ι (h0⁻¹ * h) * x ∈ K' := by
      convert hk using 1
      simp [map_mul, map_inv, mul_assoc]
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_inf, MonoidHom.mem_range,
      exists_apply_eq_apply, true_and, Subgroup.mem_map]
    refine ⟨_, hk', ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRestrictedProductEqProdStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_doubleCoset_restrictedProduct_eq_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (T : Subgroup X) (Tv : ∀ v, Subgroup (Y v)), (∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) → ∀ (F : X → ℂ) (Fv : ∀ v, Y v → ℂ), (∀ x, F x = ∏ᶠ v, Fv v (pf v x)) → (∀ v, ∀ t ∈ Tv v, ∀ y, ∀ k ∈ K v, Fv v (t * y * k) = Fv v y) → (∀ v, {q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)) | Fv v (Quotient.out q) ≠ 0}.Finite) → (∀ᶠ v in cofinite, Fv v 1 = 1 ∧ ∀ y, Fv v y ≠ 0 → ∃ t ∈ Tv v, ∃ k ∈ K v, y = t * k) → ∑ᶠ q : DoubleCoset.Quotient (T : Set X) ((⨅ v, (K v).comap (pf v) : Subgroup X) : Set X), F (Quotient.out q) = ∏ᶠ v, ∑ᶠ q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)), Fv v (Quotient.out q) := by
  first | exact @GlobalTheory.EulerAbs.finsum_doubleCoset_restr | exact GlobalTheory.EulerAbs.finsum_doubleCoset_restr | (intros; apply GlobalTheory.EulerAbs.finsum_doubleCoset_restr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogISupInt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore.RankOne

variable {K : Type} [Field K] [NumberField K]

theorem finsum_log_iSup_int {ι : Type} [Finite ι] {x : ι → 𝓞 K} (hx : x ≠ 0) :
    ∑ᶠ v : FinitePlace K, Real.log (⨆ i, v (x i)) = -Real.log (Ideal.absNorm (Ideal.span (Set.range x))) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hx
  have hi : (x i₀ : K) ≠ 0 := by exact_mod_cast hi₀
  have hz : (fun i => (x i : K)) ≠ 0 := Function.ne_iff.2 ⟨i₀, hi⟩
  have hpos : ∀ v : FinitePlace K, 0 < ⨆ i, v (x i) := fun v =>
    lt_of_lt_of_le (FinitePlace.pos_iff.2 hi) (le_ciSup (f := fun i => v (x i)) (Set.finite_range _).bddAbove i₀)
  have h := NumberField.absNorm_mul_finprod_finitePlace_eq_one hx
  rw [← Real.log_finprod hpos, eq_inv_of_mul_eq_one_right h, Real.log_inv]

theorem finsum_log_iSup_div {n : ℕ} {b : Fin n → 𝓞 K} (hb : b ≠ 0) {d : 𝓞 K} (hd : d ≠ 0) :
    ∑ᶠ v : FinitePlace K, Real.log (⨆ k, v ((b k : K) / d)) =
      Real.log (Ideal.absNorm (Ideal.span {d})) - Real.log (Ideal.absNorm (Ideal.span (Set.range b))) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hb
  have hi : (b i₀ : K) ≠ 0 := by exact_mod_cast hi₀
  have hd' : (d : K) ≠ 0 := by exact_mod_cast hd
  have hz : (fun i => (b i : K)) ≠ 0 := Function.ne_iff.2 ⟨i₀, hi⟩
  have hdz : (fun _ : Unit => d) ≠ 0 := Function.ne_iff.2 ⟨(), hd⟩
  have hdz' : (fun _ : Unit => (d : K)) ≠ 0 := Function.ne_iff.2 ⟨(), hd'⟩
  have h1 := finsum_log_iSup_int hb
  have h2 := finsum_log_iSup_int hdz
  have f1 := GlobalTheory.Adelic.HeightExt.finite_support_log_iSup hz
  have f2 := GlobalTheory.Adelic.HeightExt.finite_support_log_iSup hdz'
  rw [Set.range_const] at h2
  have e : ∀ v : FinitePlace K, Real.log (⨆ k, v ((b k : K) / d)) =
      Real.log (⨆ k, v (b k : K)) - Real.log (⨆ _ : Unit, v (d : K)) := fun v => by
    have hpos : 0 < ⨆ i, v (b i : K) :=
      lt_of_lt_of_le (FinitePlace.pos_iff.2 hi) (le_ciSup (f := fun i => v (b i : K)) (Set.finite_range _).bddAbove i₀)
    have hv : 0 < v (d : K) := FinitePlace.pos_iff.2 hd'
    rw [ciSup_const, ← Real.log_div hpos.ne' hv.ne']
    congr 1
    simp only [div_eq_mul_inv, map_mul, map_inv₀]
    exact (Real.iSup_mul_of_nonneg (inv_nonneg.2 hv.le) _).symm
  simp only [e]
  rw [finsum_sub_distrib f1 f2, h1, h2]
  ring

end GlobalTheory.HSCore.RankOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLeShiftOfSmallSectionsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubiniStudy_le_shift_of_smallSections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M B : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → SmallFam B f w → Le M (B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl) := by
  first | exact @GlobalTheory.HSNef.le_shift_of_isFS | exact GlobalTheory.HSNef.le_shift_of_isFS | (intros; apply GlobalTheory.HSNef.le_shift_of_isFS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudySubfamilyLeShiftFubiniStudyFamilyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubiniStudy_subfamily_le_shift_fubiniStudy_family : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M M' : HermLB p) (J J' : Type) [Fintype J] [Fintype J'] (f : J → X.functionField) (w : J → ℝ) (w' : J' → ℝ) (ι : J' → J) (Δ : ℝ), Function.Injective ι → IsFS M f w → IsFS M' (f ∘ ι) w' → (∀ j, w' j + Δ ≤ w (ι j)) → Le (M'.shift (fun _ => Δ) fun _ => rfl) M := by
  first | exact @GlobalTheory.HSNef.le_shift_of_isFS_sub | exact GlobalTheory.HSNef.le_shift_of_isFS_sub | (intros; apply GlobalTheory.HSNef.le_shift_of_isFS_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleGL
section
theorem GlobalTheory.FourClauses.irreducibleAdmissibleGL : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  GlobalTheory.FourClauses.adm GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
end

