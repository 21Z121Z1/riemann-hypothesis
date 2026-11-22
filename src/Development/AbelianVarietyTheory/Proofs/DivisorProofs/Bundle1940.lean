import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanThetaLocalAction
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.ArchPure

open Matrix

variable {F : Type} [Field F] [NumberField F]

def mk (a : Ainf F) (b : Af F) : AF F := (a, b)

@[simp] theorem mk_fst (a : Ainf F) (b : Af F) : (mk a b).1 = a := rfl

@[simp] theorem mk_snd (a : Ainf F) (b : Af F) : (mk a b).2 = b := rfl

theorem evI_fin (b : Af F) : evI F (((0 : Ainf F), b) : AF F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
  exact map_zero _

theorem snd_of_at {z : AF F} (hz : At (evI F) z) : z.2 = 0 := by
  have h := hz (((0 : Ainf F), (1 : Af F)) : AF F) (evI_fin 1)
  have h2 : (1 : Af F) * z.2 = 0 := congrArg Prod.snd h
  rwa [one_mul] at h2

theorem slice {κ : Type} [Fintype κ] (c : κ → Af F) :
    ∀ Ψ ∈ schA F κ, ∃ f' : SInf F κ, ∀ s : κ → mixedEmbedding.mixedSpace F,
      Ψ (fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (s i)) (c i)) = f' s := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g c • f, fun s => ?_⟩
    simp [pureA, mk, mul_comm]
  | zero => exact ⟨0, fun s => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨f1, h1⟩ := hx
    obtain ⟨f2, h2⟩ := hy
    exact ⟨f1 + f2, fun s => by rw [Pi.add_apply, h1, h2, SchwartzMap.add_apply]⟩
  | smul a x _ hx =>
    obtain ⟨f1, h1⟩ := hx
    exact ⟨a • f1, fun s => by rw [Pi.smul_apply, h1, SchwartzMap.smul_apply]⟩

theorem locA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ (C K : Set (κ → Af F)), IsCompact C ∧ IsOpen K ∧ (0 : κ → Af F) ∈ K ∧
      (∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ C) ∧
      ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → (fun i => (x' i).2 - (x i).2) ∈ K → Φ x' = Φ x := GlobalTheory.T.adelic_schwartz_support_compact_invariance

theorem locB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (C K : Set (κ → Af F)), IsCompact C → IsOpen K → (0 : κ → Af F) ∈ K →
    ∀ y : κ → AF F, ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, ∀ i, (b i).1 = 0) ∧
      ∑ b ∈ s, c b * ψ (y ⬝ᵥ b) = 1 ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ C → (∀ k ∈ K, (fun i => (x i).2) ≠ (fun i => (y i).2) + k) →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = 0 := GlobalTheory.T.character_partition_of_unity_support

theorem fibre : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) →
    (∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) → T Φ y = 0 := by
  intro F _ _ κ _ ψ T hψ hkeep hcomm Φ hΦ y hy
  obtain ⟨C, K, hC, hK, hK0, hsupp, hinv⟩ := locA Φ hΦ
  obtain ⟨s, c, hs, hy1, hm⟩ := locB ψ hψ C K hC hK hK0 y
  have hu0 : evI F (mk 0 1) = 0 := evI_fin 1
  have hub : ∀ b ∈ s, (mk 0 1 : AF F) • b = b := fun b hb => funext fun i =>
    Prod.ext (show (0 : Ainf F) * (b i).1 = (b i).1 by rw [zero_mul, hs b hb i])
      (show (1 : Af F) * (b i).2 = (b i).2 from one_mul _)
  have hsch : ∀ (b : κ → AF F) (Ψ : (κ → AF F) → ℂ), schr ψ (0, b) Ψ = fun x => ψ (x ⬝ᵥ b) * Ψ x :=
    fun b Ψ => funext fun x => by simp [schr]
  have hfac : ∀ (Ψ : (κ → AF F) → ℂ) x, (∑ b ∈ s, c b • schr ψ (0, b) Ψ) x = (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x := by
    intro Ψ x
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Pi.smul_apply, hsch, smul_eq_mul]
    ring
  have hzero : (∑ b ∈ s, c b • schr ψ (0, b) Φ) = 0 := by
    funext x
    rw [hfac, Pi.zero_apply]
    by_cases hx : Φ x = 0
    · rw [hx, mul_zero]
    · refine mul_eq_zero_of_left (hm x (hsupp x hx) fun k hk he => hx ?_) _
      have hk' : (fun i => (x i).2 - (y i).2) = k := funext fun i => by
        rw [congrFun he i, Pi.add_apply]
        abel
      have e1 : Φ x = Φ (fun i => mk (x i).1 (y i).2) := hinv _ _ (fun i => rfl) (by rw [← hk'] at hk; exact hk)
      rw [e1]
      have hz : At (evI F) (fun i => mk ((x i).1 - (y i).1) (0 : Af F)) := by
        intro u' hu'
        have h1 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hu'
        funext i
        exact Prod.ext (show u'.1 * ((x i).1 - (y i).1) = 0 by rw [h1, zero_mul])
          (show u'.2 * (0 : Af F) = 0 from mul_zero _)
      have e2 := hy _ hz
      have e3 : y + (fun i => mk ((x i).1 - (y i).1) (0 : Af F)) = fun i => mk (x i).1 (y i).2 := by
        funext i
        exact Prod.ext (show (y i).1 + ((x i).1 - (y i).1) = (x i).1 by abel)
          (show (y i).2 + 0 = (y i).2 from add_zero _)
      rwa [e3] at e2
  have hT : T (∑ b ∈ s, c b • schr ψ (0, b) Φ) = ∑ b ∈ s, c b • schr ψ (0, b) (T Φ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [map_smul]
    congr 1
    have := hcomm (mk 0 1) hu0 0 b Φ hΦ
    rwa [smul_zero, hub b hb] at this
  have e := congrFun hT y
  rw [hzero, map_zero, Pi.zero_apply, hfac, hy1, one_mul] at e
  exact e.symm

end GlobalTheory.ArchPure

namespace GlobalTheory.ArchPure

open Matrix

theorem arch_pure : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (g : UA σ G.V'.J) (h : UA σ G.W.J), At (evI F) (mat g - 1) → At (evI F) (mat h - 1) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ f₂ : SInf F (Fin a' × Fin (a + a')), om' (g, h) (pure f φ) = pure f₂ φ := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT g h hg hh f φ hφ hstd
  have hW := IsUWeilPair.isUSplitting hT.weil'
  set T := om' (g, h) with hTdef
  have hkeep : ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), T Φ ∈ schA F _ := fun Φ hΦ => hW.pres (g, h) Φ hΦ
  have hcomm : ∀ u : AF F, evI F u = 0 → ∀ p q : Fin a' × Fin (a + a') → AF F, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')),
      T (schr B.ψ (u • p, u • q) Φ) = schr B.ψ (u • p, u • q) (T Φ) := by
    intro u hu p q Φ hΦ
    set w := G.M'.co.e.symm (p, q) with hw
    have he : G.M'.co.e (u • w) = (u • p, u • q) := by
      rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h1 : u • (mat g - 1) = 0 := hg u hu
    have h2 : u • (mat h - 1) = 0 := hh u hu
    have e1 : mat g * (u • w) = u • w := by
      have : mat g * (u • w) - u • w = (u • (mat g - 1)) * w := by
        rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
      rw [h1, Matrix.zero_mul, sub_eq_zero] at this
      exact this
    have e2 : (u • w) * (mat h)ᵀ = u • w := by
      have : (u • w) * (mat h)ᵀ - u • w = w * (u • (mat h - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
      exact this
    have hact : actAB (cA σ) (g, h) (u • w) = u • w := by
      simp only [actAB]
      simp only [mat] at e1 e2
      rw [e1, e2]
    have h3 := hW.impl (g, h) (u • w) Φ hΦ
    simp only [Darboux.rho, he, hact] at h3
    exact h3
  have hstd' : ∀ᶠ w in Filter.cofinite,
      φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hstd, hT.geo.hM'.std] with w h1 h2
    rw [h1, h2]
  have hΦ : pure f φ ∈ schA F _ := GlobalTheory.TensUniq.pure_mem_schA f φ hφ hstd'
  set P : (Fin a' × Fin (a + a') → AF F) → ℂ := fun x => ∏ᶠ v, φ v fun i => evFin F v (x i) with hPdef
  have hPf : ∀ x x' : Fin a' × Fin (a + a') → AF F, (∀ i, (x i).2 = (x' i).2) → P x = P x' := by
    intro x x' hx
    simp only [hPdef]
    congr 1
    funext v
    congr 1
    funext i
    show evalV F v (x i).2 = evalV F v (x' i).2
    rw [hx i]
  have hpure : ∀ (f₀ : SInf F (Fin a' × Fin (a + a'))) x, pure f₀ φ x = f₀ (fun i => evI F (x i)) * P x :=
    fun _ _ => rfl
  by_cases h0 : ∀ x, P x = 0
  · refine ⟨f, ?_⟩
    have e : pure f φ = 0 := funext fun x => by rw [hpure, h0 x, mul_zero]; rfl
    rw [e, map_zero]
  push_neg at h0
  obtain ⟨y0, hy0⟩ := h0
  obtain ⟨f', hf'⟩ := slice (fun i => (y0 i).2) (T (pure f φ)) (hkeep _ hΦ)
  refine ⟨(P y0)⁻¹ • f', ?_⟩
  funext y
  set d : Fin a' × Fin (a + a') → AF F := fun i => mk 0 ((y0 i).2 - (y i).2) with hd
  set u : AF F := mk 0 1 with hu
  have hu0 : evI F u = 0 := evI_fin 1
  have hud : u • d = d := by
    funext i
    exact Prod.ext (show (0 : Ainf F) * 0 = 0 from mul_zero _) (show (1 : Af F) * _ = _ from one_mul _)
  have hsh : ∀ Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ, schr B.ψ (d, 0) Φ' = fun x => Φ' (x + d) :=
    fun Φ' => funext fun x => by simp [schr]
  have htr : ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')), T (fun x => Ψ (x + d)) = fun x => T Ψ (x + d) := by
    intro Ψ hΨ
    have := hcomm u hu0 d 0 Ψ hΨ
    rw [hud, smul_zero, hsh, hsh] at this
    exact this
  set c : ℂ := P y / P y0 with hc
  set Θ : (Fin a' × Fin (a + a') → AF F) → ℂ := c • fun x => pure f φ (x + d) with hΘdef
  have hΘ : Θ ∈ schA F _ := by
    refine Submodule.smul_mem _ c ?_
    have := GlobalTheory.HeisSchA.schr_mem_schA B.ψ hT.base.std (d, 0) _ hΦ
    rwa [hsh] at this
  have hvan : ∀ z, At (evI F) z → (pure f φ - Θ) (y + z) = 0 := by
    intro z hz
    have hz2 : ∀ i, (z i).2 = 0 := fun i => snd_of_at (fun u' hu' => congrFun (hz u' hu') i)
    have hevI : (fun i => evI F ((y + z + d) i)) = fun i => evI F ((y + z) i) := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (((y + z) i).1 + (0 : Ainf F)) =
        InfiniteAdeleRing.ringEquiv_mixedSpace F ((y + z) i).1
      rw [add_zero]
    have hP1 : P (y + z) = P y := hPf _ _ fun i => by
      show (y i).2 + (z i).2 = (y i).2
      rw [hz2 i, add_zero]
    have hP2 : P (y + z + d) = P y0 := hPf _ _ fun i => by
      show (y i).2 + (z i).2 + ((y0 i).2 - (y i).2) = (y0 i).2
      rw [hz2 i, add_zero]
      abel
    rw [Pi.sub_apply, hΘdef, Pi.smul_apply, smul_eq_mul, hpure, hpure, hevI, hP1, hP2, hc]
    field_simp
    ring
  have h1 := fibre B.ψ T hT.base.std hkeep hcomm _ (sub_mem hΦ hΘ) y hvan
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h1
  have h2 : T Θ y = c * T (pure f φ) (y + d) := by
    rw [hΘdef, map_smul, htr _ hΦ]
    rfl
  have hyd : y + d = fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F (y i))) ((y0 i).2) := by
    funext i
    refine Prod.ext ?_ ?_
    · show (y i).1 + 0 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)
      rw [add_zero, RingEquiv.symm_apply_apply]
    · show (y i).2 + ((y0 i).2 - (y i).2) = (y0 i).2
      abel
  rw [hpure, h1, h2, hyd, hf', SchwartzMap.smul_apply, smul_eq_mul, hc]
  field_simp

end GlobalTheory.ArchPure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjRationalPrincipalCongruence
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MsRepsFwd

theorem latOf_congr (F E : Type) [Field F] [NumberField F] [Field E] [CharZero E] [Algebra F E]
    (n M : ℕ) (L : Set (Fin n → E)) (g κ : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E))
    (δ : Matrix (Fin n) (Fin n) E) (hinj : Function.Injective (inclR (F := F) (E := E) (Af F)))
    (hκ : ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L, κ *ᵥ z - z = M • y)
    (he : δ.map (inclR (F := F) (Af F)) * g = g * κ) :
    ∀ x ∈ GlobalTheory.AdLat.latOf F g L, ∃ y ∈ GlobalTheory.AdLat.latOf F g L, δ *ᵥ x - x = M • y := by
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hx
  obtain ⟨y, hy, hzy⟩ := hκ z hz
  let i : E →+* GlobalTheory.AdLat.RA F E := inclR (F := F) (Af F)
  have hf : ∀ v : Fin n → E, GlobalTheory.AdLat.fv F v = i ∘ v := fun _ => rfl
  have e1 : i ∘ (δ *ᵥ x) = δ.map i *ᵥ (i ∘ x) := funext fun a => RingHom.map_mulVec i δ x a
  have e2 : i ∘ (δ *ᵥ x) - i ∘ x = M • (g *ᵥ y) := by
    rw [e1, ← hf x, ← hzx, Matrix.mulVec_mulVec, he, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, hzy,
      Matrix.mulVec_smul]
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have hx0 : δ *ᵥ x - x = 0 := by
      funext a
      apply hinj
      have e3 := congrFun e2 a
      simp only [Pi.sub_apply, Function.comp, zero_smul, Pi.zero_apply] at e3
      simp only [Pi.sub_apply, Pi.zero_apply, map_sub, map_zero]
      exact e3
    refine ⟨0, ⟨0, zero_mem _, ?_⟩, by rw [hx0, zero_smul]⟩
    rw [Matrix.mulVec_zero]
    funext a
    simp [GlobalTheory.AdLat.fv]
  · have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
    refine ⟨(M : E)⁻¹ • (δ *ᵥ x - x), ⟨y, hy, ?_⟩, by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hME, one_smul]⟩
    rw [hf]
    funext a
    have e3 := congrFun e2 a
    simp only [Pi.sub_apply, Function.comp, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_sub] at e3 ⊢
    rw [e3, ← map_natCast i M, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hME, map_one, one_mul]

theorem herm_mulVec {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (G δ : Matrix (Fin r) (Fin r) E)
    (h : δᵀ * G * δ.map cc = G) (x y : Fin r → E) : herm G (δ *ᵥ x) (δ *ᵥ y) = herm G x y := by
  have hh : ∀ u v : Fin r → E, herm G u v = u ⬝ᵥ (G *ᵥ (fun b => cc (v b))) := by
    intro u v
    simp only [herm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hc : (fun b => cc ((δ *ᵥ y) b)) = δ.map cc *ᵥ (fun b => cc (y b)) := by
    funext b
    simp only [cc, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hh, hh, hc, dotProduct_comm (δ *ᵥ x), Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    dotProduct_comm _ x, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

end GlobalTheory.MsRepsFwd

namespace GlobalTheory.MsRepsFwd

set_option maxHeartbeats 800000 in

theorem conj_rat_congr : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (x0 : ∀ c, Frame (X c).Ψ V.rank),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ c, x0 c ∈ (X c).dom) →
    (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (X (dict g).1).Γ,
      dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V th rfl x0 h (dict g).1))⟩) →
    (∀ c, (X c).Gm = -(V.gram)ᵀ) →
    ∀ (k : Comp) (g : GA D V), dict g = ⟨k, x0 k⟩ →
    ∀ Λk : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (Λk : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (finHom V g).1
        (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) →
    ∀ γ ∈ (X k).Γ, ∃ γ' : GL (Fin V.rank) D.host.E,
      (IsUStab (-(V.gram)ᵀ) Λk γ' ∧ ∀ x ∈ Λk, ∃ y ∈ Λk, (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = M • y) ∧
      ∀ (τ : D.host.E →+* ℂ) (hτ : τ ∈ (X k).Ψ), archM V (th k ⟨τ, hτ⟩) g * (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ =
        (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ * archM V (th k ⟨τ, hτ⟩) g := by
  intro D V Comp X dict Kf th M x0 hK hth hD hdom hA hGm k g hg Λk hΛk γ hγ
  classical
  obtain ⟨-, -, -, -, -, hfib⟩ := hD
  obtain ⟨-, hrat, -, hsur⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have hact : ∀ h, ∀ τ, mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ = archM V (th k τ) h * mat (x0 k) τ := by
    intro h τ
    show mat (x0 k) τ * ((mat (x0 k) τ)⁻¹ * Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (th k τ) h) *
      mat (x0 k) τ) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdom k τ).1),
      Matrix.one_mul]
    rfl
  have key : ∀ h ∈ GinfC V, ∃ γ'' ∈ (X k).Γ,
      dict (g * h) = ⟨k, lact γ'' (rmul (x0 k) (archMat V th rfl x0 h k))⟩ := by
    have := hA g
    rw [hg] at this
    exact this
  have h0 := ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.gramE (X k) hγ
  rw [hGm k] at h0
  have h1 : ((γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map cc)ᵀ * V.gram * γ.1 = V.gram := by
    have := congrArg (fun A => -Aᵀ) h0
    simpa [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg] using this
  have hun : ∀ τ : (X k).Ψ, ((γ.1.map τ.1).map (starRingEnd ℂ))ᵀ * V.gram.map τ.1 *
      γ.1.map τ.1 = V.gram.map τ.1 := by
    intro τ
    have hcc : (γ.1.map τ.1).map (starRingEnd ℂ) = (γ.1.map cc).map τ.1 := by
      ext a b
      exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
    rw [hcc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h1]
  obtain ⟨h, hh, hw⟩ := hsur _ hun
  have hw' : ∀ τ : (X k).Ψ, archM V (th k τ) h = γ.1.map τ.1 := hw
  obtain ⟨γ'', h1', h2⟩ := key h hh
  obtain ⟨γ₀, hγ₀, κ, hκ, hdc⟩ := hfib g (g * h) (by
    rw [hg]
    refine ⟨γ'' * γ, mul_mem h1' hγ, ?_⟩
    rw [h2]
    congr 1
    funext τ
    show γ''.1.map τ.1 * mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ =
      (γ'' * γ).1.map τ.1 * mat (x0 k) τ
    rw [hact, hw', Units.val_mul, Matrix.map_mul, Matrix.mul_assoc])
  obtain ⟨δ, hδ1, hδ2⟩ := hrat γ₀ hγ₀

  have hγ₀' := Subgroup.mem_subgroupOf.1 (show γ₀ ∈ HFinIn (AF D.host.F) _ (HSpace.gram V) from hγ₀)
  obtain ⟨δ', hδ', hδ'e⟩ := Subgroup.mem_map.1 hγ₀'
  haveI : Nontrivial (Af D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    exact (Formalism.UG.evalV D.host.F ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩).toRingHom.domain_nontrivial
  haveI : Nontrivial (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := Af D.host.F) (B := D.host.E)
      (algebraMap D.host.F D.host.E).injective).nontrivial
  have hinj : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)).injective
  have hfv : (finHom V γ₀).1 = γ₀.1.1.map
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) := rfl
  have hδδ : δ = δ' := by
    apply Units.ext
    apply Matrix.map_injective hinj
    show δ.1.map (inclR (Af D.host.F)) = δ'.1.map (inclR (Af D.host.F))
    rw [← hδ2, hfv, ← hδ'e]
    ext a b
    show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (inclR (AF D.host.F) (δ'.1 a b)) = inclR (Af D.host.F) (δ'.1 a b)
    simp [inclR]
  subst hδδ

  have hLg := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hU : (δ.1.map cc)ᵀ * V.gram * δ.1 = V.gram := by
    change Formalism.UG.cT _ δ.1 * V.gram * δ.1 = V.gram at hδ'
    convert hδ' using 3
    ext a b
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
    congr 1
  have hmat : δ.1ᵀ * -(V.gram)ᵀ * δ.1.map cc = -(V.gram)ᵀ := by
    have := congrArg (fun A => -Aᵀ) hU
    simpa [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg] using this

  obtain ⟨-, hκ2⟩ := (hK κ⁻¹).1 (inv_mem hκ)
  obtain ⟨-, hκ3⟩ := (hK κ).1 hκ
  rw [hLg.1] at hκ2 hκ3
  have hh0 : finHom V h = 1 := hh
  have hfin : finHom V γ₀ * finHom V g = finHom V g * finHom V κ⁻¹ := by
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, hh0, mul_one]
  have hfin' : finHom V γ₀⁻¹ * finHom V g = finHom V g * finHom V κ := by
    have : γ₀⁻¹ * g = g * κ * h⁻¹ := by
      calc γ₀⁻¹ * g = γ₀⁻¹ * (g * h) * h⁻¹ := by group
        _ = γ₀⁻¹ * (γ₀ * g * κ) * h⁻¹ := by rw [hdc]
        _ = g * κ * h⁻¹ := by group
    rw [← map_mul, this, map_mul, map_mul, map_inv, hh0, inv_one, mul_one]
  have hd : finHom V γ₀ = Formalism.UG.bc (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) δ := Units.ext hδ2
  have he1 : δ.1.map (inclR (F := D.host.F) (Af D.host.F)) * (finHom V g).1 = (finHom V g).1 * (finHom V κ⁻¹).1 := by
    rw [← hδ2, ← Units.val_mul, hfin, Units.val_mul]
  have he2 : (δ⁻¹).1.map (inclR (F := D.host.F) (Af D.host.F)) * (finHom V g).1 = (finHom V g).1 * (finHom V κ).1 := by
    have e0 : finHom V γ₀⁻¹ = Formalism.UG.bc (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) δ⁻¹ := by
      rw [map_inv, map_inv, hd]
    have e := congrArg Units.val hfin'
    rw [Units.val_mul, Units.val_mul, e0] at e
    exact e
  have C1 := latOf_congr D.host.F D.host.E V.rank M (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
    (finHom V g).1 (finHom V κ⁻¹).1 δ.1 hinj hκ2 he1
  have C2 := latOf_congr D.host.F D.host.E V.rank M (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
    (finHom V g).1 (finHom V κ).1 (δ⁻¹).1 hinj hκ3 he2
  have hmem : ∀ x, x ∈ Λk ↔ x ∈ GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    intro x
    rw [← SetLike.mem_coe, hΛk]
  have hcong : ∀ x ∈ Λk, ∃ y ∈ Λk, δ.1 *ᵥ x - x = M • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := C1 x ((hmem x).1 hx)
    exact ⟨y, (hmem y).2 hy, e⟩
  have hcong' : ∀ x ∈ Λk, ∃ y ∈ Λk, (δ⁻¹).1 *ᵥ x - x = M • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := C2 x ((hmem x).1 hx)
    exact ⟨y, (hmem y).2 hy, e⟩
  have hstab : ∀ x, x ∈ Λk ↔ δ.1 *ᵥ x ∈ Λk := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, e⟩ := hcong x hx
      rw [show δ.1 *ᵥ x = x + M • y by rw [← e]; abel]
      exact Λk.add_mem hx (nsmul_mem hy M)
    · intro hx
      obtain ⟨y, hy, e⟩ := hcong' _ hx
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at e
      rw [show x = δ.1 *ᵥ x + M • y by rw [← e]; abel]
      exact Λk.add_mem hx (nsmul_mem hy M)

  have hinf : infHom V γ₀ * infHom V g = infHom V g * infHom V h := by
    have h0 : infHom V κ⁻¹ = 1 := ((hK κ⁻¹).1 (inv_mem hκ)).1
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  have hm : ∀ τ a b, archM V (th k τ) (a * b) = archM V (th k τ) a * archM V (th k τ) b := by
    intro τ a b
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  refine ⟨δ, ⟨⟨herm_mulVec _ _ hmat, hstab⟩, hcong⟩, fun τ hτ => ?_⟩
  rw [← hw' ⟨τ, hτ⟩, ← hδ1 ⟨τ, hτ⟩, ← hm, ← hm]
  have e : infHom V (g * h) = infHom V (γ₀ * g) := by rw [map_mul, map_mul, hinf]
  unfold archM
  rw [e]

end GlobalTheory.MsRepsFwd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPlaceValuationResidueFieldCardEqZeroOfNotMeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffPlace_valuation_residueFieldCard_eq_zero_of_not_mem : ∀ {D : D7} (P : Pl D.host.E) (w : PlL D), ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) = 0 := by
  first | exact @GlobalTheory.UnfoldLoss.ResCardAway.vw_resCard_eq_zero | exact GlobalTheory.UnfoldLoss.ResCardAway.vw_resCard_eq_zero | (intros; apply GlobalTheory.UnfoldLoss.ResCardAway.vw_resCard_eq_zero <;> assumption)
end

