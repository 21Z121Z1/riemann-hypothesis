import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory

namespace GlobalTheory.WeilPartsF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def GfCF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (GAF σ J) :=
  ((Formalism.UG.bc (infPartF F E)).comp (matHomF σ J)).ker

def GinfCF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (GAF σ J) :=
  ((Formalism.UG.bc (finPartF F E)).comp (matHomF σ J)).ker

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)

structure IsUnitaryOnThetaF (xi0 : E) (ψ : AddChar (AF F) ℂ)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop where
  pres : ∀ p f, IsThetaFunOF σ JS JT xi0 ψ f → IsThetaFunOF σ JS JT xi0 ψ (om p f)
  cont : ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → ∀ w, Continuous fun p : GAF σ JS × GAF σ JT => om p f w
  unit : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f, IsThetaFunOF σ JS JT xi0 ψ f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

structure IsFinWeilF (xi0 : E) (ψ : AddChar (AF F) ℂ) (χS χT : (AEF F E)ˣ →* Circle)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop
    extends IsUnitaryOnThetaF σ JS JT xi0 ψ om where
  triv : ∀ g ∈ GinfCF σ JS, ∀ h ∈ GinfCF σ JT, ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GfCF σ JS, ∀ h ∈ GfCF σ JT, ∀ w₀ f, IsThetaFunOF σ JS JT xi0 ψ f →
    om (g, h) (heisOF σ JS JT xi0 ψ w₀ f) = heisOF σ JS JT xi0 ψ (actOF σ JS JT g h w₀) (om (g, h) f)
  split : ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h → ∀ x y,
    IsDetAtF σ e JS g x → IsDetAtF σ e JT h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT xi0 ψ f →
        ℓ (heisOF σ JS JT xi0 ψ u f) = ℓ f) →
      ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → ℓ (om (g, h) f) = (r : ℂ) * (splitFacOF χS χT x y : ℂ) * ℓ f

structure IsInfWeilF (xi0 : E) (ψ : AddChar (AF F) ℂ)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop
    extends IsUnitaryOnThetaF σ JS JT xi0 ψ om where
  triv : ∀ g ∈ GfCF σ JS, ∀ h ∈ GfCF σ JT, ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GinfCF σ JS, ∀ h ∈ GinfCF σ JT, ∀ w₀ f, IsThetaFunOF σ JS JT xi0 ψ f →
    om (g, h) (heisOF σ JS JT xi0 ψ w₀ f) = heisOF σ JS JT xi0 ψ (actOF σ JS JT g h w₀) (om (g, h) f)

section Lemmas

variable {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E} {ψ : AddChar (AF F) ℂ}

theorem heisOF_add (w : WOF F E nS nT) (f g : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ w (f + g) = heisOF σ JS JT xi0 ψ w f + heisOF σ JS JT xi0 ψ w g := by
  funext x
  simp only [heisOF, Pi.add_apply, mul_add]

theorem heisOF_smul (c : ℂ) (w : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ w (c • f) = c • heisOF σ JS JT xi0 ψ w f := by
  funext x
  simp only [heisOF, Pi.smul_apply, smul_eq_mul]
  ring

theorem theta_add {f g : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT xi0 ψ f) (hg : IsThetaFunOF σ JS JT xi0 ψ g) :
    IsThetaFunOF σ JS JT xi0 ψ (f + g) where
  quasi γ w := by
    simp only [Pi.add_apply]
    rw [hf.quasi, hg.quasi, mul_add]
  level := by
    obtain ⟨U, hU, hU'⟩ := hf.level
    obtain ⟨V, hV, hV'⟩ := hg.level
    exact ⟨U ⊓ V, hU.inter hV, fun u hu h0 => by rw [heisOF_add, hU' u hu.1 h0, hV' u hu.2 h0]⟩
  cont := hf.cont.add hg.cont
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).add (hg.smooth k L hL h0 w)

theorem theta_zero : IsThetaFunOF σ JS JT xi0 ψ (0 : WOF F E nS nT → ℂ) where
  quasi γ w := by simp
  level := ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext x; simp [heisOF]⟩
  cont := continuous_const
  smooth k L hL h0 w := contDiff_const

theorem theta_smul (c : ℂ) {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT xi0 ψ f) :
    IsThetaFunOF σ JS JT xi0 ψ (c • f) where
  quasi γ w := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf.quasi]
    ring
  level := by
    obtain ⟨U, hU, hU'⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisOF_smul, hU' u hu h0]⟩
  cont := hf.cont.const_smul c
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).const_smul c

variable (σ JS JT xi0 ψ) in

def thetaSubF : Submodule ℂ (WOF F E nS nT → ℂ) where
  carrier := {f | IsThetaFunOF σ JS JT xi0 ψ f}
  add_mem' := theta_add
  zero_mem' := theta_zero
  smul_mem' := fun a _ hf => theta_smul a hf

theorem mtF_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g g' : GAF σ J) : mtF σ J (g * g') = mtF σ J g * mtF σ J g' := by
  unfold mtF
  rw [map_mul]
  rfl

theorem actOF_mul (g g' : GAF σ JS) (h h' : GAF σ JT) (u : WOF F E nS nT) :
    actOF σ JS JT (g * g') (h * h') u = actOF σ JS JT g h (actOF σ JS JT g' h' u) := by
  unfold actOF
  rw [_root_.mul_inv_rev, mtF_mul, mtF_mul]
  simp only [Matrix.mul_assoc]

theorem mem_GfCF_of_supp {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {a : AEF F E} (ha : infPartF F E a = 0) {g : GAF σ J}
    (hg : ∀ i j, a * (mtF σ J g - 1) i j = (mtF σ J g - 1) i j) : g ∈ GfCF σ J := by
  rw [GfCF, MonoidHom.mem_ker, MonoidHom.comp_apply]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPartF F E ((mtF σ J g - 1) i j) = 0 := by rw [← hg i j, map_mul, ha, zero_mul]
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h
  show infPartF F E (mtF σ J g i j) = ((1 : GL (Fin n) (Ainf F ⊗[F] E)) : Matrix _ _ _) i j
  rw [h, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]

theorem infPartF_placeIdem {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdemF F v ε) :
    infPartF F E (algebraMap (AF F) (AEF F E) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 0 α ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 0 α) = 0 from rfl, TensorProduct.zero_tmul]

theorem mem_GfCF_of_suppAt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AEF F E} (he : IsSplitIdemF σ e) {g : GAF σ J}
    (hg : SuppAtF σ e J g) : g ∈ GfCF σ J := by
  obtain ⟨-, -, v, ε, h1, h2⟩ := he
  exact mem_GfCF_of_supp (h2 ▸ infPartF_placeIdem h1) hg

theorem isHeckeCharF_pow {η : (AEF F E)ˣ →* Circle} (h : IsHeckeCharF η) (n : ℕ) : IsHeckeCharF (η ^ n) :=
  ⟨h.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.2 x, one_pow]⟩

theorem resEtaF_pow {η : (AEF F E)ˣ →* Circle} (h : ResEtaF η 1) (n : ℕ) : ResEtaF (η ^ n) n :=
  ⟨h.1, fun e he a => by rw [MonoidHom.pow_apply, h.2 e he a, pow_one]⟩

theorem exists_extend {Γ V : Type} [Monoid Γ] [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (Om : Γ →* Module.End ℂ M) : ∃ om : Γ →* Module.End ℂ V, ∀ p (m : M), om p m = Om p m := by
  obtain ⟨C, hC⟩ := M.exists_isCompl
  let e := M.prodEquivOfIsCompl C hC
  refine ⟨{ toFun := fun p => e.conj ((Om p).prodMap LinearMap.id), map_one' := ?_, map_mul' := fun p q => ?_ }, ?_⟩
  · rw [map_one]
    exact (congrArg e.conj LinearMap.prodMap_id).trans e.conj_id
  · rw [map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← e.conj_comp, LinearMap.prodMap_comp,
      LinearMap.id_comp]
  · intro p m
    show e (((Om p).prodMap LinearMap.id) (e.symm m)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp [e]

end Lemmas

end GlobalTheory.WeilPartsF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.HeckeExtend

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def intF (N : ℕ) : Set (AF F) :=
  {x | ∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ x.2 = N • c}

theorem intF_one_mul {x y : AF F} (hx : x ∈ intF F 1) (hy : y ∈ intF F 1) : x * y ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  obtain ⟨d, hd, e'⟩ := hy
  refine ⟨c * d, fun v => mul_mem (hc v) (hd v), ?_⟩
  rw [one_smul] at e e' ⊢
  show x.2 * y.2 = c * d
  rw [e, e']

variable (F E) in

def SE : AddSubgroup (AF F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ s ∈ intF F 1, ∃ o : 𝓞 E, z = algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o}

theorem gen_mul {x y : AF F ⊗[F] E}
    (hx : x ∈ {z | ∃ s ∈ intF F 1, ∃ o : 𝓞 E, z = algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o})
    (hy : y ∈ {z | ∃ s ∈ intF F 1, ∃ o : 𝓞 E, z = algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o}) :
    x * y ∈ SE F E := by
  obtain ⟨s, hs, o, rfl⟩ := hx
  obtain ⟨s', hs', o', rfl⟩ := hy
  refine AddSubgroup.subset_closure ⟨s * s', intF_one_mul hs hs', o * o', ?_⟩
  have h : ((o * o' : 𝓞 E) : E) = (o : E) * o' := rfl
  rw [map_mul, h, map_mul]
  ring

theorem SE_mul {x y : AF F ⊗[F] E} (hx : x ∈ SE F E) (hy : y ∈ SE F E) : x * y ∈ SE F E := by
  induction hx using AddSubgroup.closure_induction with
  | mem g hg =>
    induction hy using AddSubgroup.closure_induction with
    | mem g' hg' => exact gen_mul hg hg'
    | zero => rw [mul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | neg a _ ha => rw [mul_neg]; exact neg_mem ha
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_mul]; exact neg_mem ha

theorem one_mem_SE : (1 : AF F ⊗[F] E) ∈ SE F E :=
  AddSubgroup.subset_closure ⟨1, ⟨1, fun v => one_mem _, by rw [one_smul]; rfl⟩, 1, by simp [Algebra.TensorProduct.one_def]⟩

variable (F E) in

def CE (N : ℕ) : AddSubgroup (AF F ⊗[F] E) := (SE F E).map (nsmulAddMonoidHom N)

theorem mem_CE {N : ℕ} {z : AF F ⊗[F] E} : z ∈ CE F E N ↔ ∃ s ∈ SE F E, N • s = z := by
  simp [CE]

theorem CE_step {N : ℕ} {x y : AF F ⊗[F] E} (hx : x - 1 ∈ CE F E N) (hy : y - 1 ∈ CE F E N) :
    x * y - 1 ∈ CE F E N := by
  obtain ⟨a, ha, ea⟩ := mem_CE.1 hx
  obtain ⟨b, hb, eb⟩ := mem_CE.1 hy
  refine mem_CE.2 ⟨a + b + N • (a * b), add_mem (add_mem ha hb) (nsmul_mem (SE_mul ha hb) N), ?_⟩
  rw [eq_add_of_sub_eq ea.symm, eq_add_of_sub_eq eb.symm]
  simp only [nsmul_eq_mul]
  ring

variable (F E) in

def WE (N : ℕ) : Subgroup (AF F ⊗[F] E)ˣ where
  carrier := {z | (z : AF F ⊗[F] E) - 1 ∈ CE F E N ∧ ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 ∈ CE F E N}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => ⟨by rw [Units.val_mul]; exact CE_step hx.1 hy.1,
    by rw [mul_inv_rev, Units.val_mul]; exact CE_step hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem cA_gen (σ : E →ₐ[F] E) (s : AF F) (o : 𝓞 E) :
    cA σ (algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o) =
      algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E (σ o) := by
  rw [map_mul, AlgHom.commutes]
  rfl

theorem cA_mem_SE (σ : E →ₐ[F] E) {z : AF F ⊗[F] E} (hz : z ∈ SE F E) : cA σ z ∈ SE F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, hs, o, rfl⟩ := hg
    rw [cA_gen]
    have : IsIntegral ℤ (σ (o : E)) := (o.2.map σ)
    exact AddSubgroup.subset_closure ⟨s, hs, ⟨σ o, this⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end GlobalTheory.HeckeExtend

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjugationStableStructure
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
open IsDedekindDomain

namespace GlobalTheory.FinClsLoc

theorem ratInt_eventually (x : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le ?_
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

theorem ratInt_eventually_away {p : ℕ} (x : ℚ) :
    ∀ᶠ w : AwayP p in Filter.cofinite,
      algebraMap ℚ (w.1.adicCompletion ℚ) x ∈ w.1.adicCompletionIntegers ℚ :=
  (Subtype.val_injective.tendsto_cofinite).eventually (ratInt_eventually x)

section

variable {C : Type} [Ring C] [Algebra ℚ C] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ C)
  (v : HeightOneSpectrum ℤ)

theorem repr_tmul_apply' (a : v.adicCompletion ℚ) (x : C) (k : κ) :
    (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr (a ⊗ₜ[ℚ] x) k =
      a * algebraMap ℚ (v.adicCompletion ℚ) (b.repr x k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]

theorem eq_sum_tmul' (y : v.adicCompletion ℚ ⊗[ℚ] C) :
    y = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ⊗ₜ[ℚ] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end

theorem intC_stab : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), ∀ᶠ w : AwayP p in Filter.cofinite,
    (∀ a b : (w.1.adicCompletion ℚ ⊗[ℚ] G.C), IntC G w a → IntC G w b → IntC G w (a * b)) ∧
    (∀ a : (w.1.adicCompletion ℚ ⊗[ℚ] G.C), IntC G w a → IntC G w (starT G.star (w.1.adicCompletion ℚ) a).unop) ∧
    IntC G w (inC G (w.1.adicCompletion ℚ) (β : G.C)) ∧ IntC G w (inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β
  set bb := Module.finBasis ℚ G.C
  have hc : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C) ×
      Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (bb t.1 * bb t.2.1) t.2.2) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ratInt_eventually_away _
  have hs : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (G.star (bb t.1)).unop t.2) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ratInt_eventually_away _
  have hb : ∀ x : G.C, ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈ w.1.adicCompletionIntegers ℚ :=
    fun x => Filter.eventually_all.2 fun k => ratInt_eventually_away _
  have hin : ∀ (w : AwayP p) (x : G.C), (∀ k, algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈
      w.1.adicCompletionIntegers ℚ) → IntC G w (inC G (w.1.adicCompletion ℚ) x) := by
    intro w x hx k
    change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr ((1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] x) k ∈ _
    rw [repr_tmul_apply', one_mul]
    exact hx k
  filter_upwards [hc, hs, hb (β : G.C), hb ((β⁻¹ : G.Cˣ) : G.C)] with w hcv hsv hbv hbv'
  refine ⟨fun y z hy hz k => ?_, fun y hy k => ?_, hin w _ hbv, hin w _ hbv'⟩
  · change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr (y * z) k ∈ _
    rw [eq_sum_tmul' bb w.1 y, eq_sum_tmul' bb w.1 z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply']
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · have hu : ∀ (f : Fin (Module.finrank ℚ G.C) → (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ᵐᵒᵖ),
        (∑ i, f i).unop = ∑ i, (f i).unop :=
      fun f => map_sum (MulOpposite.opAddEquiv : w.1.adicCompletion ℚ ⊗[ℚ] G.C ≃+ _).symm f Finset.univ
    change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr _ k ∈ _
    rw [eq_sum_tmul' bb w.1 y, map_sum, hu, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [starT_tmul, repr_tmul_apply']
    exact mul_mem (hy i) (hsv (i, k))

end GlobalTheory.FinClsLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitaryMatricesFiniteCardLe
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.SignedPerm

section General

variable {K : Type} [Field K] [NumberField K]

end General

section Host

theorem finite_and_ncard_le : ∀ (D : D7) (n : ℕ),
    {g : Matrix (Fin n) (Fin n) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.Finite ∧
    {g : Matrix (Fin n) (Fin n) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.ncard
      ≤ NumberField.Units.torsionOrder D.host.E ^ n * n.factorial := by
  intro D n
  have hcm := D.host.isCMField_hostE
  exact UpperTheory.Mu.unitary_integral_finite_and_ncard_le
    (fun φ x => IsCMField.complexEmbedding_complexConj D.host.E φ x) n

end Host

end GlobalTheory.LowRow.SignedPerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ

theorem det_submatrix_mul_of_minor {N : ℕ} {A : Type} [CommRing A] (M g h : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1))
    (u : A) (hu : ∀ I, minor h l I = u * minor g l I) (r : Fin l → Fin N) :
    ((M * h).submatrix r (Fin.castLE l.is_le)).det = u * ((M * g).submatrix r (Fin.castLE l.is_le)).det := by
  rw [det_submatrix_mul_eq_sum_minors, det_submatrix_mul_eq_sum_minors, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  have := hu I
  rw [minor, minor] at this
  rw [this]
  ring

theorem inv_mul_apply_eq_zero_of_minor {N : ℕ} {A : Type} [CommRing A] (g h : GL (Fin N) A) (l : Fin (N + 1))
    (u : Aˣ) (hu : ∀ I, minor h.1 l I = u * minor g.1 l I) (i j : Fin N) (hj : (j : ℕ) < l) (hi : (l : ℕ) ≤ i) :
    (g⁻¹ * h).1 i j = 0 := by
  have H (r : Fin l → Fin N) := det_submatrix_mul_of_minor (g⁻¹).1 g.1 h.1 l u hu r
  simp only [← Units.val_mul, inv_mul_cancel, Units.val_one] at H
  set c := (g⁻¹ * h).1
  set c₁ := c.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le) with hc₁
  have h₁ : c₁.det = u := by
    rw [hc₁, H, submatrix_one _ (Fin.castLE_injective _), det_one, mul_one]
  have h₂ : cramer c₁ᵀ (fun k => c i (Fin.castLE l.is_le k)) = 0 := by
    funext k
    have e : c₁.updateRow k (fun k => c i (Fin.castLE l.is_le k)) =
        c.submatrix (Function.update (Fin.castLE l.is_le) k i) (Fin.castLE l.is_le) := by
      ext p q
      by_cases hp : p = k
      · subst hp
        simp
      · simp [hc₁, updateRow_ne hp, Function.update_of_ne hp]
    rw [cramer_transpose_apply, e, H, det_eq_zero_of_row_eq_zero k, mul_zero, Pi.zero_apply]
    intro q
    rw [submatrix_apply, Function.update_self]
    refine one_apply_ne fun e => ?_
    have : (i : ℕ) = q := congrArg Fin.val e
    omega
  have h₃ := congrFun (mulVec_cramer c₁ᵀ (fun k => c i (Fin.castLE l.is_le k))) ⟨j, hj⟩
  rw [h₂, mulVec_zero, det_transpose, h₁] at h₃
  exact (Units.mul_right_eq_zero u).1 h₃.symm

theorem flagPt_eq_iff_below : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)) (A : Type)
    [CommRing A] (g h : ι → GL (Fin N) A),
    flagPt a l g = flagPt a l h ↔ ∀ τ i j, Below a l τ i j → ((g τ)⁻¹ * h τ).1 i j = 0 := by
  intro ι κ _ _ N a l A _ g h
  constructor
  · rintro e _ i j ⟨k, rfl, hj, hi⟩
    obtain ⟨u, hu⟩ := (flagPt_eq_iff a l g h).1 e k
    exact inv_mul_apply_eq_zero_of_minor _ _ _ u hu i j hj hi
  · intro H
    have := flagPt_mul a l g (g⁻¹ * h) fun k i j hj hi => H (a k) i j ⟨k, rfl, hj, hi⟩
    rw [mul_inv_cancel_left] at this
    exact this.symm

end GlobalTheory.FlagZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseThetaTransformHasLevelCompactFiniteSupporStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseThetaTransform_has_level_compact_finite_support : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, QuasiV ψ f → LevelV ψ f → (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, invV ψ ν 𝓓 f (x + u) = invV ψ ν 𝓓 f x) ∧ ∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, invV ψ ν 𝓓 f x ≠ 0 → fin x ∈ K := by
  first | exact @GlobalTheory.ThetaTransform.invV_level_support | exact GlobalTheory.ThetaTransform.invV_level_support | (intros; apply GlobalTheory.ThetaTransform.invV_level_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceOfLeStable
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem unitOn_of_le : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), ∀ U U' : Submodule ℂ M, UnitOn s F U → U' ≤ U →
    (∀ a b, s a = s b → ∀ u ∈ U', F a b u ∈ U') → UnitOn s F U' := by
  intro ι M _ _ _ _ s F U U' hU hle hst
  obtain ⟨hfin, -, ip, hsym, hpos, hadj⟩ := hU
  refine ⟨Submodule.finiteDimensional_of_le hle, hst, ip, ?_, ?_, ?_⟩
  · intro x hx y hy; exact hsym x (hle hx) y (hle hy)
  · intro x hx h0; exact hpos x (hle hx) h0
  · intro a b hab x hx y hy; exact hadj a b hab x (hle hx) y (hle hy)

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassPullbackVeryAmpleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEffectivePicClass_pullback_veryAmple : ∀ (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (hH : H.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∀ (φ : Y ⟶ X), Nonempty Y → GlobalTheory.EffBound.Eff (GlobalTheory.CechPic.pull φ (GlobalTheory.CechPic.cls H hH)) := by
  first | exact @GlobalTheory.EffBound.eff_pull_of_veryAmpleBy | exact GlobalTheory.EffBound.eff_pull_of_veryAmpleBy | (intros; apply GlobalTheory.EffBound.eff_pull_of_veryAmpleBy <;> assumption)
end

