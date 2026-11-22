import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSingleCharSpanMem
section
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory

noncomputable section

namespace GlobalTheory.HCF.FormsSub

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem isAutForm_zero : IsAutForm (0 : Sm E a) where
  left γ g := rfl
  level := by
    have : {k | finRep E a k (0 : Sm E a) = 0} = Set.univ := Set.eq_univ_of_forall fun k => map_zero _
    rw [this]; exact isOpen_univ
  kfin := by
    refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp
  zfin := by
    refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp
  growth g := ⟨0, 0, fun y => by simp⟩

theorem isAutForm_add {φ ψ : Sm E a} (hφ : IsAutForm φ) (hψ : IsAutForm ψ) : IsAutForm (φ + ψ) where
  left γ g := by
    change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
    rw [hφ.left, hψ.left]
  level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
    ((hφ.level.inter hψ.level).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
      have h1 : finRep E a k φ = φ := hk.1
      have h2 : finRep E a k ψ = ψ := hk.2
      change finRep E a k (φ + ψ) = φ + ψ
      rw [map_add, h1, h2]
  kfin := by
    have := hφ.kfin
    have := hψ.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  zfin := by
    have := hφ.zfin
    have := hψ.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) ⊔
      Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) '' Zalg E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe, map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩) (Submodule.subset_span ⟨z, hz, rfl⟩)
  growth g := by
    obtain ⟨C1, N1, h1⟩ := hφ.growth g
    obtain ⟨C2, N2, h2⟩ := hψ.growth g
    refine ⟨|C1| + |C2|, N1 + N2, fun y => ?_⟩
    have hy := one_le_height y
    have e1 : height y ^ N1 ≤ height y ^ (N1 + N2) := pow_le_pow_right₀ hy (by omega)
    have e2 : height y ^ N2 ≤ height y ^ (N1 + N2) := pow_le_pow_right₀ hy (by omega)
    have p1 : 0 ≤ height y ^ N1 := by positivity
    have p2 : 0 ≤ height y ^ N2 := by positivity
    change ‖φ.1 _ + ψ.1 _‖ ≤ _
    calc ‖φ.1 (g * infGL E a y) + ψ.1 (g * infGL E a y)‖
        ≤ ‖φ.1 (g * infGL E a y)‖ + ‖ψ.1 (g * infGL E a y)‖ := norm_add_le _ _
      _ ≤ C1 * height y ^ N1 + C2 * height y ^ N2 := add_le_add (h1 y) (h2 y)
      _ ≤ |C1| * height y ^ (N1 + N2) + |C2| * height y ^ (N1 + N2) := by
          exact add_le_add ((mul_le_mul_of_nonneg_right (le_abs_self C1) p1).trans
              (mul_le_mul_of_nonneg_left e1 (abs_nonneg _)))
            ((mul_le_mul_of_nonneg_right (le_abs_self C2) p2).trans
              (mul_le_mul_of_nonneg_left e2 (abs_nonneg _)))
      _ = _ := by ring

theorem isAutForm_smul (c : ℂ) {φ : Sm E a} (hφ : IsAutForm φ) : IsAutForm (c • φ) where
  left γ g := by
    change c • φ.1 _ = c • φ.1 _
    rw [hφ.left]
  level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
    (hφ.level.mem_nhds (by simp)) fun k hk => by
      have h1 : finRep E a k φ = φ := hk
      change finRep E a k (c • φ) = c • φ
      rw [map_smul, h1]
  kfin := by
    have := hφ.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  zfin := by
    have := hφ.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩)
  growth g := by
    obtain ⟨C, N, h1⟩ := hφ.growth g
    refine ⟨‖c‖ * C, N, fun y => ?_⟩
    change ‖c • φ.1 _‖ ≤ _
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 y) (norm_nonneg _)

theorem foldr_lin (χ : Module.End ℂ (Sm E a) → ℂ) (c : ℂ) (φ ψ : Sm E a) (zs : List (Module.End ℂ (Sm E a))) :
    zs.foldr (fun z f => z f - χ z • f) (c • φ + ψ) =
      c • zs.foldr (fun z f => z f - χ z • f) φ + zs.foldr (fun z f => z f - χ z • f) ψ := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.foldr_cons]
    rw [ih, map_add, map_smul]
    module

theorem foldr_zero (χ : Module.End ℂ (Sm E a) → ℂ) (zs : List (Module.End ℂ (Sm E a))) :
    zs.foldr (fun z f => z f - χ z • f) (0 : Sm E a) = 0 := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp only [List.foldr_cons, ih, map_zero, smul_zero, sub_zero]

end GlobalTheory.HCF.FormsSub

open GlobalTheory.HCF.FormsSub in

theorem GlobalTheory.HCF.formsGL_single_span : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ),
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W {χ} N), φ ∈ formsGL E a L W {χ} N := by
  intro E _ _ _ a L W χ N
  let S : Submodule ℂ (Sm E a) :=
    { carrier := formsGL E a L W {χ} N
      zero_mem' := by
        refine ⟨isAutForm_zero, fun k _ => map_zero _, fun g => ?_, χ, rfl, fun zs _ _ => foldr_zero χ zs⟩
        have : (fun k : Kinf E a => (cptRep E a k (0 : Sm E a)).1 g) = 0 := by
          funext k; simp
        rw [this]; exact W.zero_mem
      add_mem' := by
        rintro φ ψ ⟨a1, b1, c1, χ1, e1, d1⟩ ⟨a2, b2, c2, χ2, e2, d2⟩
        rw [Set.mem_singleton_iff] at e1 e2
        rw [e1] at d1
        rw [e2] at d2
        refine ⟨isAutForm_add a1 a2, fun k hk => by rw [map_add, b1 k hk, b2 k hk], fun g => ?_, χ, rfl,
          fun zs hl hz => ?_⟩
        · have : (fun k : Kinf E a => (cptRep E a k (φ + ψ)).1 g) =
              (fun k : Kinf E a => (cptRep E a k φ).1 g) + (fun k : Kinf E a => (cptRep E a k ψ).1 g) := by
            funext k; simp
          rw [this]; exact W.add_mem (c1 g) (c2 g)
        · have := foldr_lin χ 1 φ ψ zs
          rw [one_smul, one_smul] at this
          rw [this, d1 zs hl hz, d2 zs hl hz, add_zero]
      smul_mem' := by
        rintro c φ ⟨a1, b1, c1, χ1, e1, d1⟩
        rw [Set.mem_singleton_iff] at e1
        rw [e1] at d1
        refine ⟨isAutForm_smul c a1, fun k hk => by rw [map_smul, b1 k hk], fun g => ?_, χ, rfl,
          fun zs hl hz => ?_⟩
        · have : (fun k : Kinf E a => (cptRep E a k (c • φ)).1 g) = c • (fun k : Kinf E a => (cptRep E a k φ).1 g) := by
            funext k; simp
          rw [this]; exact W.smul_mem c (c1 g)
        · have := foldr_lin χ c φ 0 zs
          rw [add_zero, foldr_zero, add_zero] at this
          rw [this, d1 zs hl hz, smul_zero] }
  intro φ hφ
  exact (Submodule.span_le (p := S)).2 le_rfl hφ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFormNegOfPairBounds
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg MvPolynomial

noncomputable section

namespace GlobalTheory.FockSecondSwap

variable {p q r s : ℕ}

def swapLn (p q r s : ℕ) : Ln p q r s ≃ Ln p q s r :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.sumComm _ _)

def lsg (l : Ln p q r s) : ℂ := if linePos l then 1 else -1

def eps : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

def tJ (X : Mat p q) : Mat p q := Matrix.of fun a b => eps a * eps b * X b a

theorem eps_mul_self (a : Ix p q) : eps a * eps a = 1 := by
  rcases a with a | a <;> simp [eps]

theorem linePos_swapLn (l : Ln p q r s) : linePos (swapLn p q r s l) = !linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> rfl

theorem trace_tJ (X : Mat p q) : (tJ X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, tJ, Matrix.of_apply, eps_mul_self, one_mul]

theorem rename_raiB (l : Ln p q r s) (f : Pol p q r s) :
    rename (swapLn p q r s) (raiB l f) = lsg l • lowB (swapLn p q r s l) (rename (swapLn p q r s) f) := by
  have hd := pderiv_rename (R := ℂ) (swapLn p q r s).injective l f
  unfold raiB lowB lsg
  rw [linePos_swapLn]
  cases h : linePos l <;> simp [hd]

theorem rename_lowB (l : Ln p q r s) (f : Pol p q r s) :
    rename (swapLn p q r s) (lowB l f) = -(lsg l) • raiB (swapLn p q r s l) (rename (swapLn p q r s) f) := by
  have hd := pderiv_rename (R := ℂ) (swapLn p q r s).injective l f
  unfold raiB lowB lsg
  rw [linePos_swapLn]
  cases h : linePos l <;> simp [hd]

theorem rename_omE (l l' : Ln p q r s) (f : Pol p q r s) :
    rename (swapLn p q r s) (omE l l' f) =
      -(lsg l * lsg l') • omE (swapLn p q r s l') (swapLn p q r s l) (rename (swapLn p q r s) f) := by
  have hc := congrArg (fun T : Module.End ℂ (Pol p q s r) => T (rename (swapLn p q r s) f))
    (GlobalTheory.FockCasimir.lowB_mul_raiB (swapLn p q r s l) (swapLn p q r s l'))
  simp only [Module.End.mul_apply, LinearMap.add_apply] at hc
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply, map_add, rename_raiB, rename_lowB,
    LinearMap.map_smul, hc]
  by_cases h : l = l'
  · subst h
    simp only [if_true, LinearMap.smul_apply, Module.End.one_apply, map_smul]
    have h1 : lsg l = 1 ∨ lsg l = -1 := by unfold lsg; split_ifs <;> simp
    rcases h1 with h1 | h1 <;> rw [h1] <;> module
  · have h' : swapLn p q r s l ≠ swapLn p q r s l' := fun e => h ((swapLn p q r s).injective e)
    simp only [h, h', Ne.symm h', if_false, LinearMap.zero_apply, add_zero, map_zero]
    module

def swapM (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) : Matrix (Ln p q s r) (Ln p q s r) ℂ :=
  Matrix.of fun m m' => lsg ((swapLn p q r s).symm m') * lsg ((swapLn p q r s).symm m) *
    Z ((swapLn p q r s).symm m') ((swapLn p q r s).symm m)

theorem rename_omAct (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) (f : Pol p q r s) :
    rename (swapLn p q r s) (omAct p q r s Z f) = -(omAct p q s r (swapM Z) (rename (swapLn p q r s) f)) := by
  simp only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, rename_omE]
  have e : ∀ h : Ln p q s r → Ln p q s r → Pol p q s r,
      ∑ m, ∑ m', h m m' = ∑ l, ∑ l', h (swapLn p q r s l') (swapLn p q r s l) := by
    intro h
    rw [Finset.sum_comm, ← (swapLn p q r s).sum_comp]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← (swapLn p q r s).sum_comp]
  rw [e]
  simp only [swapM, Matrix.of_apply, Equiv.symm_apply_apply, ← Finset.sum_neg_distrib, smul_smul, neg_smul,
    smul_neg, mul_neg]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  ring_nf

theorem kron_apply (X : Mat p q) (a b : Ix p q) (c d : Ix r s) :
    (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat r s) X (a, c) (b, d) = X a b * (1 : Mat r s) c d := by
  simp [Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply]

theorem swapM_kron (X : Mat p q) :
    swapM ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat r s) X) =
      (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat s r) (tJ X) := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [swapM, Matrix.of_apply, kron_apply, tJ, swapLn, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.refl_symm, Equiv.refl_apply, Equiv.sumComm_symm, Equiv.sumComm_apply, Prod.map]
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d <;>
    simp [lsg, linePos, eps, Matrix.one_apply] <;> split_ifs <;> simp_all [eq_comm]

theorem rename_fockAct1 (X : Mat p q) (f : Pol p q r s) :
    rename (swapLn p q r s) (fockAct1 p q r s X f) = -(fockAct1 p q s r (tJ X) (rename (swapLn p q r s) f)) := by
  simp only [fockAct1, LinearMap.comp_apply]
  rw [rename_omAct, swapM_kron]

end GlobalTheory.FockSecondSwap

namespace GlobalTheory.RealLift

open GlobalTheory.FockSecondSwap

theorem hasForm_swap {P Q R S : ℕ} {x : ℚ} (h : HasForm P Q S R x) : HasForm P Q R S (-x) := by
  obtain ⟨l, hl0, hl⟩ := h
  refine ⟨l.comp (rename (swapLn P Q R S)).toLinearMap, fun h0 => hl0 (LinearMap.ext fun f => ?_), fun X f => ?_⟩
  · have := LinearMap.congr_fun h0 (rename (swapLn P Q R S).symm f)
    simpa [rename_rename, Equiv.self_comp_symm, rename_id] using this
  · simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [rename_fockAct1, map_neg, hl, trace_tJ]
    push_cast
    ring

theorem hasForm_neg_of_formEx : FormEx → ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), P ≤ S → Q ≤ R → 0 < k → 0 < k' →
    x - Formalism.BasicNotions.TH.cPair S R = k → x + Formalism.BasicNotions.TH.cPair S R = k' → HasForm P Q R S (-x) :=
  fun hF P Q R S x k k' h1 h2 h3 h4 h5 h6 => hasForm_swap (hF P Q S R x k k' h1 h2 h3 h4 h5 h6)

end GlobalTheory.RealLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoArchimedeanAdelicPureTensor
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.ArchHeisPure

open scoped Classical Matrix

theorem exists_phase_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (a : V)
    (f : SchwartzMap V ℂ) : ∃ g : SchwartzMap V ℂ, ∀ x,
      g x = Complex.exp (-(2 * Real.pi * Complex.I) * ((L x + c : ℝ) : ℂ)) * f (x + a) := by
  refine ⟨SchwartzMap.smulLeftCLM ℂ (GlobalTheory.LinPhaseSeminorm.phaseLine c 1 ∘ ⇑L) (SchwartzMap.compSubConstCLM ℂ (-a) f),
    fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase L c 1),
    ← GlobalTheory.LinPhaseSeminorm.phase_eq]
  simp

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

variable (F) in

def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

def trForm (c : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c)
      map_add' := fun y y' => by rw [add_dotProduct, map_add]
      map_smul' := fun r y => by rw [smul_dotProduct, map_smul]; rfl }

theorem evHom_apply (a : AF F) : evHom F a = evI F a := rfl

theorem trForm_apply (c y : κ → mixedEmbedding.mixedSpace F) :
    trForm c y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c) := rfl

theorem schr_pureA [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {w : (κ → AF F) × (κ → AF F)}
    (hw : At (evI F) w) (f : SInf F κ) :
    ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, schr ψ w (pureA F f h) = pureA F f₁ h := by
  obtain ⟨p, q⟩ := w
  obtain ⟨g, hg⟩ := exists_phase_translate (trForm fun i => evI F (q i))
    (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (p ⬝ᵥ q)))) (fun i => evI F (p i)) f
  refine ⟨g, fun h => funext fun x => ?_⟩
  have hfin : (fun i => ((x + p) i).2) = fun i => (x i).2 := by
    funext i
    have h0 : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h1 : (1 : Af F) * (p i).2 = 0 := congrArg (fun z : (κ → AF F) × (κ → AF F) => (z.1 i).2) (hw _ h0)
    change (x i).2 + (p i).2 = _
    rw [one_mul] at h1
    rw [h1, add_zero]
  have harch : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + p) i).1) =
      (fun i => evI F (x i)) + fun i => evI F (p i) := by
    funext i
    exact map_add (evHom F) (x i) (p i)
  have hAt : At (evI F) (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q)) := by
    intro v hv
    have hq : v • q = 0 := congrArg Prod.snd (hw v hv)
    rw [smul_add, ← dotProduct_smul, smul_eq_mul, mul_left_comm, ← smul_eq_mul v, ← dotProduct_smul, hq]
    simp
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q))) =
      trForm (fun i => evI F (q i)) (fun i => evI F (x i)) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (p ⬝ᵥ q))) := by
    rw [← evHom_apply, map_add, map_add, RingHom.map_dotProduct, trForm_apply]
    rfl
  simp only [schr, pureA]
  rw [hψ.2.2 _ hAt, htr, hfin, harch, ← mul_assoc, ← hg]
  rfl

theorem rho_pureA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    IsStd ψ → ∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f : SInf F κ,
      ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d hψ u hu f
  refine schr_pureA hψ (fun r hr => ?_) f
  rw [← map_smul, hu r hr, map_zero]

end GlobalTheory.ArchHeisPure

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoSplitArchimedeanFinite
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.HeisSplit

theorem schr_add_of_orth {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b : (κ → R) × (κ → R)) (h1 : a.1 ⬝ᵥ b.2 = 0) (h2 : b.1 ⬝ᵥ a.2 = 0) (φ : (κ → R) → ℂ) :
    schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add, h1, h2]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  ring

theorem dot_eq_zero {R : Type} [CommRing R] {κ : Type} [Fintype κ] (e : R) (a c : κ → R) (h : e • a = 0) :
    a ⬝ᵥ (e • c) = 0 := by
  rw [dotProduct_smul, ← smul_dotProduct, h, zero_dotProduct]

section

variable (F : Type) [Field F] [NumberField F]

noncomputable def finAd (z : Af F) : AF F := ((0 : InfiniteAdeleRing F), z)

theorem finAd_mul (x : AF F) : finAd F x.2 * finAd F 1 = x * finAd F 1 := by
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * 0 = x.1 * 0
    simp
  · rfl

theorem finAd_idem : finAd F 1 * finAd F 1 = finAd F 1 := by
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * 0 = 0
    simp
  · show (1 : Af F) * 1 = 1
    simp

theorem evI_finAd : evI F (finAd F 1) = 0 := by
  exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem mul_finAd_of (t : AF F) (ht : evI F t = 0) : t * finAd F 1 = t := by
  have h : t.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 ht
  refine Prod.ext ?_ ?_
  · show t.1 * 0 = t.1
    simp [h]
  · show t.2 * 1 = t.2
    simp

theorem schr_pureA [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (c : (κ → AF F) × (κ → AF F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ) :
    schr ψ (finAd F 1 • c) (pureA F f h) =
      pureA F f (fun z => schr ψ (finAd F 1 • c) (fun x => h fun i => (x i).2) fun i => finAd F (z i)) := by
  funext x
  have e1 : (fun i => finAd F (x i).2) ⬝ᵥ (finAd F 1 • c).2 = x ⬝ᵥ (finAd F 1 • c).2 := by
    simp only [dotProduct, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, ← mul_assoc, finAd_mul]
  have e2 : ∀ i, ((x + (finAd F 1 • c).1) i).1 = (x i).1 := by
    intro i
    show (x i).1 + 0 * (c.1 i).1 = (x i).1
    simp
  have e3 : ∀ i, (((fun i => finAd F (x i).2) + (finAd F 1 • c).1) i).2 = ((x + (finAd F 1 • c).1) i).2 := fun i => rfl
  simp only [schr, pureA, e1, e2, e3]
  ring

end

theorem rho_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    ∀ w : Matrix α β (AE F E),
    ∃ (u : Matrix α β (AE F E)) (H : ((κ → Af F) → ℂ) → (κ → Af F) → ℂ), At (evI F) u ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        ∀ (f f₁ : SInf F κ) (h : (κ → Af F) → ℂ),
          (∀ h' : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F f h') = pureA F f₁ h') →
            d.rho ψ (actB (cA σ) g w) (pureA F f h) = pureA F f₁ (H h) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d w
  have hu : finAd F 1 • (w - finAd F 1 • w) = 0 := by
    rw [smul_sub, smul_smul, finAd_idem, sub_self]
  refine ⟨w - finAd F 1 • w,
    fun h z => schr ψ (finAd F 1 • d.e w) (fun x => h fun i => (x i).2) fun i => finAd F (z i), ?_, ?_⟩
  · intro t ht
    rw [smul_sub, smul_smul, mul_finAd_of F t ht, sub_self]
  · intro g hg f f₁ h hyp
    have hg' := hg _ (evI_finAd F)
    rw [smul_sub, sub_eq_zero] at hg'
    have hv : actB (cA σ) g (finAd F 1 • w) = finAd F 1 • w := by
      unfold actB
      rw [Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.transpose_smul, hg', Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.mul_smul, Matrix.mul_one]
    have hw : actB (cA σ) g w = actB (cA σ) g (w - finAd F 1 • w) + finAd F 1 • w := by
      have : actB (cA σ) g (w - finAd F 1 • w) = actB (cA σ) g w - actB (cA σ) g (finAd F 1 • w) := by
        unfold actB
        rw [Matrix.sub_mul]
      rw [this, hv, sub_add_cancel]
    have ha : finAd F 1 • d.e (actB (cA σ) g (w - finAd F 1 • w)) = 0 := by
      rw [← map_smul]
      unfold actB
      rw [← Matrix.smul_mul, hu, Matrix.zero_mul, map_zero]
    rw [← hyp, hw]
    unfold Darboux.rho
    rw [map_add, map_smul, schr_add_of_orth, schr_pureA]
    · exact dot_eq_zero _ _ _ (congrArg Prod.fst ha)
    · rw [dotProduct_comm]
      exact dot_eq_zero _ _ _ (congrArg Prod.snd ha)

end GlobalTheory.HeisSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramDetEqNormSqBasisDetMulStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFam_gram_det_eq_normSq_basis_det_mul : ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] (nm : HermFam F V) (σ : F →+* ℂ) (d : ℕ) (b : Module.Basis (Fin d) F V) (v : Fin d → V), (nm.gram σ v).det = ((Complex.normSq (σ (b.det v)) : ℝ) : ℂ) * (nm.gram σ ⇑b).det := by
  first | exact @GlobalTheory.GramChange.gram_det | exact GlobalTheory.GramChange.gram_det | (intros; apply GlobalTheory.GramChange.gram_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnOffCoordinateHyperplanesOfPoincareBoStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_offCoordinateHyperplanes_of_poincareBound : ∀ {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (g : V n → ℂ) (C : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → ContinuousOn g (offHyp S U) → (∀ v ∈ offHyp S U, v ∉ K → g v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ‖g v‖ ≤ C * ∏ a, (poinWt S v a)⁻¹ ^ 2) → IntegrableOn g (offHyp S U) := by
  first | exact @GlobalTheory.GoodTop.integrableOn_offHyp_of_norm_le_poin | exact GlobalTheory.GoodTop.integrableOn_offHyp_of_norm_le_poin | (intros; apply GlobalTheory.GoodTop.integrableOn_offHyp_of_norm_le_poin <;> assumption)
end

