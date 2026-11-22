import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijectiveToPushforwardComp

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirLowerBoundOnStableSubspace
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult GlobalTheory.TensorHW GlobalTheory.BlockReps

noncomputable section

namespace GlobalTheory.CasimirBound

variable {R S : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
  {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}

lemma unitK_adj (hB : IsUnitary actW B) (a b : Ix R S) (x y : W) :
    B (unitK actW a b x) y = B x (unitK actW b a y) := by
  by_cases h : sameBlock a b
  · have h' : sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    rw [unitK, unitK, if_pos h, if_pos h']
    exact hB.2.2 a b h x y
  · have h' : ¬ sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    simp [unitK, h, h']

lemma casK_adj (hB : IsUnitary actW B) (x y : W) :
    B (casK actW x) y = B x (casK actW y) := by
  simp only [casK, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [unitK_adj hB, unitK_adj hB]

lemma finrank_map_add_inf_ker [FiniteDimensional ℂ W] (U : Submodule ℂ W) (f : Module.End ℂ W) :
    Module.finrank ℂ (U.map f) + Module.finrank ℂ (U ⊓ LinearMap.ker f : Submodule ℂ W) =
      Module.finrank ℂ U := by
  have h := (f.domRestrict U).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq U, Submodule.map_comap_subtype] at h
  exact h

lemma finiteRing_sq_sub_mul_sq_eq_of_card [FiniteDimensional ℂ W] (hL : IsKLieAct actW)
    (hd : ∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) (hB : IsUnitary actW B) (c₀ : ℚ) (n : ℕ) :
    ∀ U : Submodule ℂ W, Module.finrank ℂ U ≤ n → KStable actW U →
    (∀ (ν : Ix R S → ℚ) y, y ∈ U → IsHW actW ν y → c₀ < casVal ν) →
    ∀ x ∈ U, x ≠ 0 → (c₀ : ℝ) * (B x x).re < (B x (casK actW x)).re := by
  induction n with
  | zero =>
    intro U hU _ _ x hx h0
    have : U = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hU)
    subst this
    exact absurd ((Submodule.mem_bot ℂ).1 hx) h0
  | succ n ih =>
    intro U hU hUs hc x hx h0
    obtain ⟨ν, v, hvU, hv⟩ := exists_hw hL hUs (fun w _ => hd w) ((Submodule.ne_bot_iff U).2 ⟨x, hx, h0⟩)
    set c : ℂ := ((casVal ν : ℚ) : ℂ) with hcdef
    set f : Module.End ℂ W := casK actW - c • 1 with hf
    set E : Submodule ℂ W := U ⊓ LinearMap.ker f with hE
    set U₂ : Submodule ℂ W := U.map f with hU₂
    have hstar : starRingEnd ℂ c = c := by rw [hcdef, map_ratCast]
    have hfadj : ∀ y z, B (f y) z = B y (f z) := by
      intro y z
      simp only [hf, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        LinearMap.map_smulₛₗ₂, LinearMap.sub_apply, hstar, casK_adj hB, smul_eq_mul, LinearMap.smul_apply, map_smul]
    have hfU : ∀ u ∈ U, f u ∈ U := fun u hu => U.sub_mem (casK_mem hUs hu) (U.smul_mem _ hu)
    have hU₂U : U₂ ≤ U := Submodule.map_le_iff_le_comap.2 fun u hu => hfU u hu
    have hcomm : ∀ a b, sameBlock a b → ∀ y, actW (Eab a b) (f y) = f (actW (Eab a b) y) := by
      intro a b hab y
      rw [← Module.End.mul_apply, ← Module.End.mul_apply]
      congr 1
      exact ((casK_comm hL hab).sub_right ((Commute.one_right _).smul_right _)).eq
    have hU₂s : KStable actW U₂ := by
      intro Z hZ w hw
      obtain ⟨u, hu, rfl⟩ := hw
      refine kc_ind actW U₂ (f u) (fun a b hab => ?_) hZ
      rw [hcomm a b hab]
      exact ⟨_, hUs _ (isKC_Eab hab) u hu, rfl⟩
    have horth : ∀ e ∈ E, ∀ z ∈ U₂, B e z = 0 := by
      intro e he z hz
      obtain ⟨u, -, rfl⟩ := hz
      rw [← hfadj, LinearMap.mem_ker.1 he.2, map_zero, LinearMap.zero_apply]
    have hdisj : E ⊓ U₂ = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Submodule.mem_bot]
      by_contra hz0
      have := hB.2.1 z hz0
      rw [horth z hz.1 z hz.2] at this
      simp at this
    have hdim : Module.finrank ℂ U₂ + Module.finrank ℂ E = Module.finrank ℂ U :=
      finrank_map_add_inf_ker U f
    have hsup : E ⊔ U₂ = U := by
      have h1 : Module.finrank ℂ (E ⊔ U₂ : Submodule ℂ W) + Module.finrank ℂ (E ⊓ U₂ : Submodule ℂ W) =
          Module.finrank ℂ E + Module.finrank ℂ U₂ := Submodule.finrank_sup_add_finrank_inf_eq E U₂
      rw [hdisj, finrank_bot] at h1
      exact Submodule.eq_of_le_of_finrank_eq (sup_le inf_le_left hU₂U) (by omega)
    have hvE : v ∈ E := ⟨hvU, by simp [hf, casK_hw hL hv.2, hcdef]⟩
    have hlt : Module.finrank ℂ U₂ < Module.finrank ℂ U := by
      apply Submodule.finrank_lt_finrank_of_lt
      refine lt_of_le_of_ne hU₂U fun h => hv.1 ?_
      have : v ∈ E ⊓ U₂ := ⟨hvE, h ▸ hvU⟩
      rwa [hdisj, Submodule.mem_bot] at this
    have hcv := hc ν v hvU hv
    obtain ⟨e, he, z, hz, rfl⟩ := Submodule.mem_sup.1 (hsup ▸ hx : x ∈ E ⊔ U₂)
    have hce : casK actW e = c • e := by
      have := LinearMap.mem_ker.1 he.2
      simp only [hf, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      exact sub_eq_zero.1 this
    have hze : B z e = 0 := by rw [← hB.1, horth e he z hz, star_zero]
    have hcz : B e (casK actW z) = 0 := by
      rw [← casK_adj hB, hce, LinearMap.map_smulₛₗ₂, horth e he z hz, smul_zero]
    have hIH : z ≠ 0 → (c₀ : ℝ) * (B z z).re < (B z (casK actW z)).re := fun hz0 =>
      ih U₂ (by omega) hU₂s (fun ν y hy => hc ν y (hU₂U hy)) z hz hz0
    have ex1 : B (e + z) (e + z) = B e e + B z z := by
      simp only [map_add, LinearMap.add_apply, horth e he z hz, hze]; ring
    have ex2 : B (e + z) (casK actW (e + z)) = c * B e e + B z (casK actW z) := by
      simp only [map_add, LinearMap.add_apply, hce, LinearMap.map_smul, hcz, hze, smul_eq_mul]; ring
    have hcr : (c * B e e).re = (casVal ν : ℝ) * (B e e).re := by
      simp [hcdef, Complex.mul_re]
    have hc' : (c₀ : ℝ) < (casVal ν : ℝ) := by exact_mod_cast hcv
    rw [ex1, ex2, Complex.add_re, Complex.add_re, hcr]
    by_cases he0 : e = 0
    · subst he0
      have hz0 : z ≠ 0 := by simpa using h0
      have := hIH hz0
      simp only [map_zero, LinearMap.zero_apply, Complex.zero_re, mul_zero, zero_add]
      exact this
    · have hpos := hB.2.1 e he0
      have h2 : (c₀ : ℝ) * (B z z).re ≤ (B z (casK actW z)).re := by
        by_cases hz0 : z = 0
        · subst hz0; simp
        · exact (hIH hz0).le
      nlinarith

theorem casimir_form_gt : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (c₀ : ℚ), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsUnitary actW B → ∀ U : Submodule ℂ W, KStable actW U →
    (∀ (ν : Ix R S → ℚ) y, y ∈ U → IsHW actW ν y → c₀ < GlobalTheory.BlockReps.casVal ν) →
    ∀ x ∈ U, x ≠ 0 → (c₀ : ℝ) * (B x x).re < (B x (GlobalTheory.BlockReps.casK actW x)).re := by
  intro R S W _ _ _ actW B c₀ hL hd hB U hU hc
  exact finiteRing_sq_sub_mul_sq_eq_of_card hL hd hB c₀ _ U le_rfl hU hc

end GlobalTheory.CasimirBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmQuadraticCharacterEqProdRealSigns
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.EtaSignReal

open GlobalTheory.QuadSymbol GlobalTheory.IdeleNormChar GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eq_signToCircle [Algebra.IsQuadraticExtension F E] (η : (AF F)ˣ →* Circle) (hη : IsEtaF E η) :
    η = signToCircle.comp (normSign E) := by
  obtain ⟨-, h1, h3, h4⟩ := hη
  refine eq_signToCircle_comp _ η (fun a ha => ?_) h4
  obtain ⟨t, x, hx⟩ := (normSign_eq_one_iff E a).1 ha
  rw [← div_mul_cancel a (toUnits F (AdeleRing (𝓞 F) F) t), map_mul, ← hx, h3 x, one_mul]
  exact h1 t

theorem finComp_eq_one {a : (AF F)ˣ} (ha : At (evI F) ((a : AF F) - 1)) : finComp a = 1 := by
  have h := ha ((0 : Ainf F), (1 : Af F)) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _)
  have h2 : ((a : AF F) - 1).2 = 0 := by
    have := congrArg Prod.snd h
    change (1 : Af F) * ((a : AF F) - 1).2 = 0 at this
    rwa [one_mul] at this
  have h3 : (a : AF F).2 = 1 := sub_eq_zero.1 (h2 : (a : AF F).2 - 1 = 0)
  funext v
  apply Units.ext
  change (a : AF F).2 v = 1
  rw [h3]
  rfl

theorem normSign_eq_prod [Algebra.IsQuadraticExtension F E] {a : (AF F)ˣ} (ha : finComp a = 1) :
    normSign E a = ∏ w : InfinitePlace F, eta F E w.Completion (infComp a w) := by
  change etaProd F E (finComp a) (infComp a) = _
  rw [etaProd, ha]
  have : ∀ v : HeightOneSpectrum (𝓞 F), eta F E (v.adicCompletion F) ((1 : FinFam F) v) = 1 :=
    fun v => eta_eq_one_iff.2 (one_mem _)
  simp only [this, finprod_one, one_mul]

theorem ringEquivReal_neg {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) {δ : F} (hδ : δ ≠ 0) {θ : E} (hθ : σ θ = -θ) (h1 : θ * θ = algebraMap F E δ) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap F w.Completion δ) < 0 := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set z := τ.1 θ
  have hz : star z = -z := by rw [← hcm.2.2.2 τ.1 θ, hθ, map_neg]
  have hre : z.re = 0 := by
    have := congrArg Complex.re hz
    simp at this
    linarith
  have hc : ((e (algebraMap F w.Completion δ) : ℝ) : ℂ) = z * z := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    have h5 : InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion δ) = w.embedding δ :=
      InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm δ)
    rw [h5, ← τ.2, RingHom.comp_apply, ← h1, map_mul]
  have hr := congrArg Complex.re hc
  simp only [Complex.ofReal_re, Complex.mul_re, hre, zero_mul, zero_sub] at hr
  have hne : e (algebraMap F w.Completion δ) ≠ 0 := (map_ne_zero e).2 ((map_ne_zero _).2 hδ)
  refine lt_of_le_of_ne ?_ hne
  rw [hr]
  nlinarith [mul_self_nonneg z.im]

theorem mem_normGroup_iff_pos {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) (x : (w.Completion)ˣ) :
    x ∈ normGroup F E w.Completion ↔
      0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (x : w.Completion) := by
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.1.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hne : ∃ x, σ x ≠ x := by
    by_contra h
    push_neg at h
    haveI := hcm.2.1
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ.1)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    exact (hcm.2.2.2 τ.1 x).symm.trans (by rw [h x])
  obtain ⟨δ, b, hδ, h0, hσb, h1⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hcm.2.2.1 hinv hne
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  have hneg := ringEquivReal_neg hcm hw τ hδ0 hσb h1
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  rw [mem_normGroup_iff_form b h0 h1]
  constructor
  · rintro ⟨p, q, h⟩
    have hx0 : e (x : w.Completion) ≠ 0 := (map_ne_zero e).2 x.ne_zero
    have h2 : e (x : w.Completion) = e p ^ 2 - e (algebraMap F w.Completion δ) * e q ^ 2 := by
      rw [h, map_sub, map_mul, map_pow, map_pow]
    refine lt_of_le_of_ne ?_ hx0.symm
    rw [h2]
    nlinarith [sq_nonneg (e p), sq_nonneg (e q)]
  · intro hpos
    refine ⟨e.symm (Real.sqrt (e x)), 0, ?_⟩
    apply e.injective
    simp [Real.sq_sqrt hpos.le]

theorem piInf_idFF {w : InfinitePlace F} (hw : w.IsReal) (τ : EmbOver E w) (a : (AF F)ˣ) :
    piInf τ ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion) : ℝ) : ℂ) := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  change infEmb τ (compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) a)) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  change infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]
  rfl

theorem eta_eq_prod_sign : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ B hB η hη a ha
  have hcm := hB.cm
  haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  haveI := hcm.1
  rw [eq_signToCircle η hη, MonoidHom.comp_apply, normSign_eq_prod (finComp_eq_one ha), map_prod]
  rw [show ((∏ w : InfinitePlace F, signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) =
      ∏ w : InfinitePlace F, ((signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) from
    map_prod Circle.coeHom _ _]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : w.IsReal := IsTotallyReal.isReal w
  rw [piInf_idFF hw]
  set r := InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion)
  have hx := mem_normGroup_iff_pos hcm hw (B.emb w) (infComp a w)
  have hr0 : r ≠ 0 := (map_ne_zero _).2 (infComp a w).ne_zero
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hpos : 0 < r
  · rw [eta_eq_one_iff.2 (hx.2 hpos), map_one, abs_of_pos hpos, div_self (by exact_mod_cast hr0)]
    rfl
  · have hneg : r < 0 := lt_of_le_of_ne (not_lt.1 hpos) hr0
    rw [eta_eq_neg_one_iff.2 (fun h => hpos (hx.1 h)), abs_of_neg hneg]
    change ((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = _
    rw [if_neg (by decide)]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr0)]

end GlobalTheory.EtaSignReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
section
noncomputable section

namespace GlobalTheory.ThK.UnipDom

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def fA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → AE F E) : AE F E :=
  v ⬝ᵥ (incM F J *ᵥ fun i => cA σ (w i))

def coA (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) (g : UA σ J) :
    Fin d₁ → AE F E :=
  fun j => fA σ J (mat g *ᵥ (incM F H'.ι *ᵥ Pi.single j 1)) (incV F H'.y)

def coC (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) (g : UA σ J) : AE F E :=
  fA σ J (mat g *ᵥ incV F H'.y) (incV F H'.y)

end GlobalTheory.ThK.UnipDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

noncomputable section

namespace GlobalTheory.Poinc.Tors

def LiesOver {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (w₀ : W0 U) (g : GtPtF D.toPre F) (w : Frm D.toPre F 1 g.b)
    (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ wk : Frm D.toPre F k g.b,
    (∀ z J, Good D.toPre.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k) → wk.IsGen →
    ∀ (s : SecA A F k) (s' : Fam D.toPre F k) (v : F),
      U.ExpandsF F k w₀ s s' → ValAt s x fr v → SumF I F (coef s' g wk) v

section
open GlobalTheory.UT.PullExp GlobalTheory.FieldBaseChange

theorem coef_twistPull : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∀ (E : EndU U.toUnifPre), Function.Injective E.h → ∀ (k' k : ℕ), 1 ≤ k → 1 ≤ k' → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen) → (∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ) ∧ ∀ (w₀ : W0 U.toUnifPre) (ρ), NormW U.toUnifPre w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') s s', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w' : Frm D.toPre F k' g.b) (w : Frm D.toPre F k g'.b), w'.IsGen → w.IsGen → (∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J) → (∀ χ, coef s' g w' (E.h χ) = coef s g' w χ) ∧ ∀ β, β ∉ Set.range E.h → coef s' g w' β = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ E hh k' k hk hk' ⟨β₀, hβ₀⟩
  have hGF := hL.1.globalFns
  have := hI.1
  have := hI.2.2.2
  have := E.homG
  obtain ⟨β, hβ, hβ'⟩ := exists_normalised U.LG.isLB E.aG k' k β₀ hβ₀
  obtain ⟨κ₀, hκ₀, hrel⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL R I hI D A G hG U E k' k β hβ hβ'
  refine ⟨⟨κ₀, hκ₀⟩, ?_⟩
  intro w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' s s' ⟨v, hv, n, c, σ, f, h₁, h₂, h₃⟩ ⟨v', hv', hs'⟩ htw κ hκ g g' hg w' w hw' hw₁ hww
  choose σ' f' p₁ p₂ p₃ p₄ using fun i => GlobalTheory.T.pullback_section_endomorphism_expansion R I D A G U.toUnifPre E hh k' k β hβ κ₀ hκ₀.1 hrel (σ i) (f i) (h₁ i)
  have tw := GlobalTheory.T.endU_twist_of_iso hGF R I D A G U.toUnifPre E F k' k β hβ hβ' w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' v v' hv hv' htw
  have H := secLin_of_expandsG U.toUnifPre (IsAdicComplete.le_jacobson_bot I) F k' v' s' hs' n c σ' f' p₁
    ((secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => by
      rw [tw y J hJ, GlobalTheory.BoxExpansion.secLin_val h₂ _ y hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e₁ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
        rw [← Over.comp_left, whiskerLeft_fst]
      have e₂ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫ UnifPre.gFK (G := G) F =
          UnifPre.gFK (G := G) F ≫ E.aG.left := by
        rw [UnifPre.gFK, ← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, Category.assoc,
          Category.assoc]
        exact congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)
      rw [p₂ i _ _ y J hJ, gs_scal, gs_scal, e₁, e₂, Category.id_comp, Category.id_comp, _root_.mul_assoc])
  refine ⟨fun χ => CoefBasic.coef_eq fun z J hJ => ?_, fun b hb => CoefBasic.coef_eq fun z J hJ => ?_⟩
  · have a := CoefBasic.isCoef_coef g' hw₁ χ s z J hJ
    have e : g.b.left ≫ D.toPre.P.A.hom = (TF (R := R) F).hom := Over.w g.b
    have e' : g'.b.left = g.b.left ≫ E.aB.left := congrArg (fun q => q.left) hg.1
    rw [sval_comb (h₃ χ) _ z hJ, hg.2 χ z J hJ, ← hww z J hJ, e', normd_val_eq hGF hκ hκ₀ _ z J hJ] at a
    rw [sval_comb (H (E.h χ)) _ z hJ]
    simp only [p₃ _ χ _ _ z J hJ, e, ← _root_.mul_assoc, ← Finset.sum_mul]
    have e₃ : (rigV D.toPre (TF (R := R) F).hom z J).val ^ k' =
        (rigV D.toPre (TF (R := R) F).hom z J).val ^ k * (rigV D.toPre (TF (R := R) F).hom z J ^ ((k' : ℤ) - k)).val := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_natCast,
        ← zpow_add, add_sub_cancel]
    rw [e₃, ← _root_.mul_assoc, a]
    simp only [Units.val_mul]
    ring
  · rw [sval_comb (H b) _ z hJ, CoefBasic.cst_eq, map_zero, zero_mul, Finset.sum_eq_zero, zero_mul, zero_mul]
    intro i _
    exact (congrArg _ ((congrArg (gs _ z _) (p₄ i b hb _)).trans (gs_zero' _ z _ (hJ.mem _ _)))).trans (mul_zero _)

end

section
open GlobalTheory.UT.EvalZero GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

theorem sumF_origin : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∃ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen) ∧ (∀ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen → ∃ w₀, NormW U.toUnifPre w₀ ρ) ∧ ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (k : ℕ) (t : SecA A F k) s, U.ExpandsF F k w₀ t s → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b), g.IsZero → FrmOne w → ∀ c : F, (∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val) → SumF I F (coef s g w) c := by
  intro _ R _ _ _ I hI D A G _ _ _ U F _ _
  refine ⟨exists_gen_pt (Y := Spec (CommRingCat.of (FractionRing R))) A.isLB
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
      (fun y => Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _) _ _,
    exists_normW U.toUnifPre, ?_⟩
  rintro w₀ ρ h k t s ⟨σ', hR, n, c, σ, f, hE, hσ, hs⟩ g w hg hw b hb
  choose a ha using fun i α => exists_value D.toPre k α (f i α)
  choose x hx using fun i => exists_coeff (A := R) U.LG.isLB (σ i) (eSec G) (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig k)
    (powGen_isGen _ _ _ _ U.LG.rigGen k) (fun W _ f => by simp)
  have hx' : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good U.LG.L z J →
      sval (σ i) (r ≫ eSec G) z J = Geo.Tor.cst r z (x i) * (val (L := U.LG.L) U.LG.rig r z J ^ k).val :=
    fun i Z r z J hJ => (hx i Z r z J hJ).trans (by rw [val_pow])
  rw [value_comb U.toUnifPre F h t σ' hR c σ hσ x hx' b hb,
    funext fun α => coef_comb F s c f α (hs α) (fun i => a i α) (fun i => ha i α) g w hg hw]
  exact sumF_comb hI F _ c _ _ fun i => sumF_map I F (a i) (x i) fun e =>
    value_sub_sum_mem U.toUnifPre e k (σ i) (f i) (hE i e) (x i) (hx' i) (a i) (ha i)

end

end GlobalTheory.Poinc.Tors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CofinitePlacesRealizePrimes
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

open IsDedekindDomain Rat.HeightOneSpectrum

theorem exists_finset_forall_prime_awayP_padic :
    ∀ (p : ℕ) [Fact p.Prime] (P : AwayP p → Prop), (∀ᶠ w in Filter.cofinite, P w) →
    ∃ S : Finset ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ w : AwayP p, P w ∧ Nonempty (w.1.adicCompletion ℚ ≃+* ℚ_[ℓ]) := by
  intro p _ P hP
  have hfin : {w : AwayP p | ¬ P w}.Finite := hP
  refine ⟨insert p (hfin.toFinset.image fun w => ((primesEquiv (R := ℤ) w.1 : Nat.Primes) : ℕ)), ?_⟩
  intro ℓ hℓ hS
  have hℓp : ℓ ≠ p := fun h => hS (by simp [h])
  let q : Nat.Primes := ⟨ℓ, hℓ.out⟩
  let v : HeightOneSpectrum ℤ := (primesEquiv (R := ℤ)).symm q
  have hv : ((primesEquiv (R := ℤ) v : Nat.Primes) : ℕ) = ℓ := by
    show ((primesEquiv (R := ℤ) ((primesEquiv (R := ℤ)).symm q) : Nat.Primes) : ℕ) = ℓ
    rw [Equiv.apply_symm_apply]
  have hne : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    have h1 := span_natGenerator (R := ℤ) v
    have h2 : natGenerator v = ℓ := hv
    rw [h, h2, Ideal.map_span] at h1
    simp only [Set.image_singleton, map_natCast] at h1
    have h3 : (ℓ : ℤ) ∣ (p : ℤ) := Ideal.mem_span_singleton.1 (h1 ▸ Ideal.mem_span_singleton_self _)
    have h4 : (p : ℤ) ∣ (ℓ : ℤ) := Ideal.mem_span_singleton.1 (h1.symm ▸ Ideal.mem_span_singleton_self _)
    exact hℓp (Nat.dvd_antisymm (Int.natCast_dvd_natCast.1 h3) (Int.natCast_dvd_natCast.1 h4))
  refine ⟨⟨v, hne⟩, ?_, ?_⟩
  · by_contra hw
    apply hS
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨v, hne⟩, hfin.mem_toFinset.2 hw, hv⟩)
  · exact ⟨((Padic.adicCompletionEquiv ℤ q).symm : _ ≃+* ℚ_[(q : ℕ)])⟩

end GlobalTheory.FinClsLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfCechPicardClassEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.Div

theorem coh_subsingleton_of_cls_eq : ∀ (X : Scheme.{0}) (M N : LB X) (hM : M.IsLB) (hN : N.IsLB),
    cls M hM = cls N hN → ∀ q : ℕ, Subsingleton (coh (LB.toMod M) q) →
      Subsingleton (coh (LB.toMod N) q) := by
  intro X M N hM hN e q h
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule X) hM hN e
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q
    ((Twist.unitTwistIso M).symm ≪≫ i ≪≫ Twist.unitTwistIso N)).toEquiv.subsingleton_congr.1 h

end GlobalTheory.Div
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfDisjointOpenCover
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem coh_subsingleton_of_disjoint_cover : ∀ (X : Scheme.{0}) (M : LB X) (κ : Type) (U : κ → X.Opens), M.IsLB → ⨆ c, U c = ⊤ → (Pairwise fun a b => Disjoint (U a) (U b)) → ∀ q : ℕ, (∀ c, Subsingleton (coh (LB.toMod (M.pull (U c).ι)) q)) → Subsingleton (coh (LB.toMod M) q) := by
  intro X M κ U hM hc hd q h
  have hj : ∀ (i : κ) (r : ℤ), (U i).ι.appTop (algebraMap ℤ Γ(X, ⊤) r) =
      algebraMap ℤ Γ((U i).toScheme, ⊤) r := fun i r => by simp
  have hs : ∀ i, Subsingleton (coh ((LB.toMod M).restrict (U i).ι) q) := fun i =>
    (cohOn.mapIso ℤ ⊤ q ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app _ ≪≫
      LB.pullbackIso hM (U i).ι)).toEquiv.subsingleton_congr.2 (h i)
  exact (coh.disjointRestrictEquiv ℤ (fun i => (U i).ι) hj (by simpa using hc)
    (by simpa using hd) (LB.toMod M) q).toEquiv.subsingleton

end GlobalTheory
end

