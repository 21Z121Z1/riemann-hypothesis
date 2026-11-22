import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0275
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0277
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0454
import Formalism.LocalToGlobal.GroupLattices.StabilizerCount.StabiliserTrivialOfTiedChain

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RepsOfEqImage
section
noncomputable section

namespace GlobalTheory.TwU.XiTwo

section Abs

open Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Mv
open Formalism.L2.KerInert Formalism.L2.KerInert.PullbackComparison Formalism.L2.KerInert.RepComb

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [DecidableEq W]
  (H : Sesq V) (α : V → ℂ) (H₁ : Sesq W) (α₁ : W → ℂ) (T : V ≃+ W)

omit [DecidableEq W] in
theorem brk_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (y t : V) : brk H₁ (T y) (T t) = brk H y t := by
  unfold brk altE
  rw [hH]

theorem hatS_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (vol : ℝ) (SA : Finset V) (Φ : W → ℂ) (x y : V) :
    hatS H₁ vol (SA.image T) (fun s => Φ (s - T x)) (T y) = hatS H vol SA (fun s => Φ (T (s - x))) y := by
  unfold hatS
  rw [Finset.card_image_of_injective _ T.injective, Finset.sum_image (fun a _ b _ h => T.injective h)]
  congr 2
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [brk_map H H₁ T hH]
  simp only [map_sub]

omit [DecidableEq W] in
theorem opU_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (x : V) (e : W → ℂ) (z : V) :
    opU H₁ (T x) e (T z) = opU H x (fun v => e (T v)) z := by
  unfold opU
  rw [hH, hH, ← map_add]

theorem xiL_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (hα : ∀ x, α₁ (T x) = α x) (vol : ℝ) (SX SA SB : Finset V)
    (Φ e : W → ℂ) (z : V) :
    xiL H₁ α₁ vol (SX.image T) (SA.image T) (SB.image T) Φ e (T z) =
      xiL H α vol SX SA SB (fun v => Φ (T v)) (fun v => e (T v)) z := by
  rw [xiL_expand, xiL_expand, Finset.sum_image (fun a _ b _ h => T.injective h)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_image (fun a _ b _ h => T.injective h)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hatS_map H H₁ T hH, hα, hα, hH, hH, ← map_add, opU_map H H₁ T hH]

omit [Module ℂ V] [Module ℂ W] in

theorem isReps_image {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S)
    (h1 : ∀ x, T x ∈ M₁ ↔ x ∈ Λ₁) (h2 : ∀ x, T x ∈ M₂ ↔ x ∈ Λ₂) : IsReps M₁ M₂ (S.image T) := by
  first
  | exact @_root_.GlobalTheory.RepresentativesImage.isReps_image
  | exact _root_.GlobalTheory.RepresentativesImage.isReps_image
  | (apply _root_.GlobalTheory.RepresentativesImage.isReps_image <;> assumption)
  | (intros; apply _root_.GlobalTheory.RepresentativesImage.isReps_image <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RepresentativesImage.isReps_image <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RepresentativesImage.isReps_image ..)

omit [Module ℂ V] [Module ℂ W] in

theorem repsOf_eq_image {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} (hS : ∃ S, IsReps Λ₁ Λ₂ S)
    (h1 : ∀ x, T x ∈ M₁ ↔ x ∈ Λ₁) (h2 : ∀ x, T x ∈ M₂ ↔ x ∈ Λ₂) :
    ∃ S : Finset V, IsReps Λ₁ Λ₂ S ∧ repsOf M₁ M₂ = S.image T := by
  classical
  obtain ⟨S, hS⟩ := hS
  have hex : ∃ S₁, IsReps M₁ M₂ S₁ := ⟨_, isReps_image T hS h1 h2⟩
  have hR : IsReps M₁ M₂ (repsOf M₁ M₂) := by
    unfold repsOf
    exact Classical.epsilon_spec hex
  refine ⟨(repsOf M₁ M₂).image T.symm, isReps_image T.symm hR (fun x => ?_) (fun x => ?_), ?_⟩
  · rw [← h1, AddEquiv.apply_symm_apply]
  · rw [← h2, AddEquiv.apply_symm_apply]
  · rw [Finset.image_image]
    have : (T ∘ T.symm : W → W) = id := funext fun x => T.apply_symm_apply x
    rw [this, Finset.image_id]

end Abs

section Main

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiL_two : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (H₁ : Formalism.L2.Th1.H.Sesq W) (α₁ : W → ℂ) (T : V ≃+ W), (∀ x y, H₁ (T x) (T y) = H x y) → (∀ x, α₁ (T x) = α x) → ∀ (A B Λ : AddSubgroup V) (A₁ B₁ Λ₁ : AddSubgroup W), SplitHyp H α A B Λ → (∀ x, T x ∈ Λ₁ ↔ x ∈ Λ) → (∀ x, T x ∈ A₁ ↔ x ∈ A) → (∀ x, T x ∈ B₁ ↔ x ∈ B) → (∃ S, Formalism.L2.Th1.H.IsReps Λ A S) → (∃ S, Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) S) → (∃ S, Formalism.L2.Th1.H.IsReps Λ B S) → ∀ (vol : ℝ) (θ Φ : W → ℂ), (fun v => θ (T v)) ∈ Formalism.L2.Th1.H.fixedBy H α Λ → InvOn A B (fun v => Φ (T v)) → ∀ z, xiL H₁ α₁ vol (repsOf Λ₁ A₁) (repsOf B₁ (Λ₁ ⊓ A₁)) (repsOf Λ₁ B₁) Φ θ (T z) = xiL H α vol (repsOf Λ A) (repsOf B (Λ ⊓ A)) (repsOf Λ B) (fun v => Φ (T v)) (fun v => θ (T v)) z := by
  intro V W _ _ _ _ H α H₁ α₁ T hH hα A B Λ A₁ B₁ Λ₁ hyp hΛ hA hB hX hSA hSB vol θ Φ hθ hΦ z
  classical
  have hΛA : ∀ x, T x ∈ Λ₁ ⊓ A₁ ↔ x ∈ Λ ⊓ A := fun x => by
    rw [AddSubgroup.mem_inf, AddSubgroup.mem_inf, hΛ, hA]
  obtain ⟨SX, rX, eX⟩ := repsOf_eq_image T hX hΛ hA
  obtain ⟨SA, rA, eA⟩ := repsOf_eq_image T hSA hB hΛA
  obtain ⟨SB, rB, eB⟩ := repsOf_eq_image T hSB hΛ hB
  rw [eX, eA, eB, xiL_map H α H₁ α₁ T hH hα]
  exact twist_representatives V H α A B Λ hyp _ _ _ _ _ _ (GlobalTheory.TwU.KerMove.repsOf_of_exists hX) (GlobalTheory.TwU.KerMove.repsOf_of_exists hSA)
    (GlobalTheory.TwU.KerMove.repsOf_of_exists hSB) rX rA rB vol _ hθ _ hΦ z

end Main

end GlobalTheory.TwU.XiTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatWDCharPolChars
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.SatChar

variable {Ω : Type} [Field Ω] {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]
  {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem charPol_satWD (h : IsPlaceOver A w) (n : ℕ) (B : Multiset ℂˣ) (g : Weil h) :
    (satWD h n B).charPol g = (B.map fun b : ℂˣ =>
      X - C ((((normV w : ℕ) : ℂ) ^ (((((1 : ℝ) - n) / 2 : ℝ)) : ℂ)) ^ deg g * ((b : ℂ)⁻¹) ^ deg g)).prod := by
  classical
  have hs : ∀ {ι : Type} (c : ℂ) (d : ι → ℂ), c • diagEnd d = diagEnd (fun i => c * d i) := fun c d =>
    LinearMap.ext fun v => funext fun i => by simp [mul_assoc]
  rw [satWD, WD.lpUnr, WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.diag_ρ, hs, charpoly_diagEnd,
    ← Finset.prod_map_val]
  rw [Multiset.map_univ (B.map fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ))
    (fun z : ℂ => X - C ((((normV w : ℕ) : ℂ) ^ ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) ^ deg g * ((WD.unitOf z : ℂˣ) : ℂ) ^ deg g)),
    Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [WD.coe_unitOf (by simp), Units.val_inv_eq_inv_val]

def ordHom (w : HeightOneSpectrum (𝓞 E)) : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (ord (w.adicCompletion E) x)) fun x y => by
    rw [ord_mul, ofAdd_add]

theorem unram_art {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : ∀ x : (w.adicCompletion E)ˣ, Valued.v (x : w.adicCompletion E) = 1 → χ x = 1)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) (g : Weil h) :
    χ (a g) = χ ϖ ^ (-deg g) := by
  have h1 : ord (w.adicCompletion E) ϖ = 1 := by
    rw [SphCompletion.ord_completion, hϖ, WithZero.log_exp]; simp
  have h2 : ord (w.adicCompletion E) (a g * ϖ ^ deg g) = 0 := by
    have := congrArg Multiplicative.toAdd (map_mul (ordHom w) (a g) (ϖ ^ deg g))
    rw [map_zpow] at this
    simp only [ordHom, MonoidHom.mk'_apply, toAdd_ofAdd, toAdd_mul, toAdd_zpow, smul_eq_mul] at this
    rw [this, ha.ord_eq, h1]; ring
  have h3 : Valued.v ((a g * ϖ ^ deg g : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [SphCompletion.ord_completion, neg_eq_zero] at h2
    have h0 : Valued.v ((a g * ϖ ^ deg g : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
    rw [← WithZero.exp_log h0, h2, WithZero.exp_zero]
  have h4 : a g = (a g * ϖ ^ deg g) * ϖ ^ (-deg g) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [h4, map_mul, hχ _ h3, one_mul, map_zpow]

theorem absPow_art {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) (s : ℝ)
    (g : Weil h) :
    (absPow (w.adicCompletion E) (s : ℂ) (a g) : ℂ) = (((normV w : ℕ) : ℂ) ^ (s : ℂ)) ^ deg g := by
  have hq : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by
    have := GlobalTheory.WeilDeligne.one_lt_normV w
    exact_mod_cast (zero_lt_one.trans this)
  rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hq.le, ← Complex.ofReal_zpow,
    ← Complex.ofReal_cpow (zpow_pos hq _).le]
  congr 1
  rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, mul_comm]

theorem satWD_charPol_chars : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (n : ℕ) (ξ ξ' : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)), (∀ j, ξ' j = ξ j * absPow (w.adicCompletion E) ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) → (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) → ∀ ϖ : (w.adicCompletion E)ˣ, Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, (satWD h n (Finset.univ.val.map fun j => ξ j ϖ)).charPol g = ∏ j, (X - C ((ξ' j (a g) : ℂˣ) : ℂ)) := by
  intro Ω _ E _ _ _ _ w A h n ξ ξ' hξ' hun ϖ hϖ a ha g
  rw [charPol_satWD, Multiset.map_map, Finset.prod_map_val]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Function.comp_apply]
  rw [hξ' j, MonoidHom.mul_apply, Units.val_mul, unram_art ha (ξ j) (hun j) ϖ hϖ g, absPow_art ha]
  congr 2
  rw [Units.val_zpow_eq_zpow_val, zpow_neg, inv_zpow, mul_comm]

end GlobalTheory.SatChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeamGLInjective
section
noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

def CongX {E : Type} [Field E] [NumberField E] {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (h : Sp E N ≃ₗ[E] Sp E N) : Prop :=
  ∀ a b, Formalism.L2.Col.IntAt P ((((qOf P : ℕ) : E) ^ n)⁻¹ * (LinearMap.toMatrix' h.toLinearMap - 1) a b)

section Seam

variable {D : D7} {X : Fields} (s : Seam D X)

def seamLE {n : ℕ} (g : GL (Fin n) D.host.E) : Sp X.E n ≃ₗ[X.E] Sp X.E n :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv X.E (Fin n → X.E)
    (Matrix.GeneralLinearGroup.toLin (bc (s.iE.symm : D.host.E →+* X.E) g))

theorem seamGL_seamLE {n : ℕ} (g : GL (Fin n) D.host.E) : seamGL s (seamLE s g) = g := by
  ext a b
  simp [seamGL, seamLE, bc]

end Seam

end GlobalTheory.TwU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardKernelDataWithStandardReadersStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardKernelData_with_standardBaseLevels : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned := by
  first | exact @GlobalTheory.Pdv.stdKer_stdRd | exact GlobalTheory.Pdv.stdKer_stdRd | (intros; apply GlobalTheory.Pdv.stdKer_stdRd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroChartOfMemberLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.AtTrue.ZeroChart

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem latAt_eCls0 (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (c : (I.stp u I.mu0 0).Cl) :
    I.latAt u a 0 (I.eCls0 l u a c) = I.latAt u I.mu0 0 c := by
  have e : I.eCls0 l u a c = I.cl0 u a (l.idx0 a).some c := rfl
  unfold TC.latAt
  rw [dif_pos (Nat.zero_le _), dif_pos (Nat.zero_le _), e, ClsZero.stepZero_corresponding_representatives_same_deco hI]

theorem range_eCls0 (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (c : (I.stp u I.mu0 0).Cl)
    (γ : GL (Fin (B.R.N 0)) B.host.E) :
    γ ∈ (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) (I.eCls0 l u a c)).range ↔
      γ ∈ (MemChart.stM (Chart0.lvG I I.mu0) (Chart0.lvQ I I.mu0) ((I.Tp I.mu0).pref u 0) (I.pref u I.mu0 0) c).range := by
  rw [Chart0.stab_range0 I hI, Chart0.stab_range0 I hI]
  have e : I.eCls0 l u a c = I.cl0 u a (l.idx0 a).some c := rfl
  rw [e, ClsZero.stepZero_corresponding_representatives_same_deco hI]

theorem map_conj_mul {G : Type} [Group G] (U : Subgroup G) (y k : G) (hk : k ∈ U) :
    U.map (MulAut.conj (y * k)).toMonoidHom = U.map (MulAut.conj y).toMonoidHom := by
  ext g
  constructor
  · rintro ⟨x, hx, hg⟩
    refine ⟨k * x * k⁻¹, (conj_mem_iff hk x).2 hx, Eq.trans ?_ hg⟩
    show y * (k * x * k⁻¹) * y⁻¹ = y * k * x * (y * k)⁻¹
    group
  · rintro ⟨x, hx, hg⟩
    refine ⟨k⁻¹ * x * k, by simpa using (conj_mem_iff (inv_mem hk) x).2 hx, Eq.trans ?_ hg⟩
    show y * k * (k⁻¹ * x * k) * (y * k)⁻¹ = y * x * y⁻¹
    group

end GlobalTheory.TwU.AtTrue.ZeroChart

end

namespace GlobalTheory.TwU.AtTrue.ZeroChart

open scoped TensorProduct

set_option maxHeartbeats 4000000 in

theorem chart_of_member : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClsTied (D := (I.rec7 l Z)) u 0 (Nat.zero_le _)) (κ : (I.stp u I.mu0 0).Cl → K.lev.U), (∀ c s, (K.stabI c s).1 = (I.stp u I.mu0 0).gam c.1 s.1) → ∃ K0 : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), (K0 ()).lev.Lb = K.lev.Lb ∧ (K0 ()).lev.Uloc = K.lev.Uloc ∧ (K0 ()).lev.U = K.lev.U ∧ (∀ (x : (K0 ()).lev.U) (x' : K.lev.U), x.1 = x'.1 → (K0 ()).lev.chi x = K.lev.chi x') ∧ (∀ c, ((K0 ()).y ⟨I.eCls0 l u a c, rfl⟩).1 = (K.y c).1 * (κ c).1) ∧ ∀ c s, ((K0 ()).stabI c s).1 = (I.stp u a 0).gam c.1.1 s.1 := by
  intro B X I hI hP l Z u a Q K κ hK
  have hi : 0 ≤ B.R.m := Nat.zero_le _
  let e := I.eCls0 l u a
  have hU : ∀ c, (κ c).1 ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) :=
    fun c => ((K.lev.U_eq _).1 (κ c).2).1
  let κU : ∀ c, UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) :=
    fun c => ⟨(κ c).1, hU c⟩
  have hL : ∀ c, (κ c).1 ∈ levelAfL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 hi) K.lev.Lb := fun c =>
    (GlobalTheory.LatticeStabLocal.mem_levelAfL_iff _ _ _ _ _ _ K.lev.Lb_fin _).2
      ⟨hU c, fun v => K.lev.Uloc_lev v (((K.lev.U_eq _).1 (κ c).2).2 v)⟩
  have hlat : ∀ c'', I.latAt u a 0 c'' = I.latAt u I.mu0 0 (e.symm c'') := by
    intro c''
    obtain ⟨c, rfl⟩ := e.surjective c''
    rw [e.symm_apply_apply]
    exact latAt_eCls0 I hI l u a c
  have hrng : ∀ c'' (γ : GL (Fin (B.R.N 0)) B.host.E),
      γ ∈ (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'').range ↔
      γ ∈ (MemChart.stM (Chart0.lvG I I.mu0) (Chart0.lvQ I I.mu0) ((I.Tp I.mu0).pref u 0) (I.pref u I.mu0 0) (e.symm c'')).range := by
    intro c'' γ
    obtain ⟨c, rfl⟩ := e.surjective c''
    rw [e.symm_apply_apply]
    exact range_eCls0 I hI l u a c γ
  have hmem : ∀ c'' (s : (I.stp u a 0).Stab c''),
      MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'' s ∈
        UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) 0 hi) := by
    intro c'' s
    obtain ⟨t, ht⟩ := (hrng c'' _).1 ⟨s, rfl⟩
    rw [← ht]
    exact (congrArg (fun g => g ∈ UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) 0 hi))
      (hK (e.symm c'') t)).mp (K.stabI (e.symm c'') t).2
  have hcls : ∀ c, (Quotient.mk'' (K.y c * κU c) : Cls K.lev) = Quotient.mk'' (K.y c) := fun c => by
    refine (DoubleCoset.eq _ _ _ _).2 ⟨1, one_mem _, (κU c)⁻¹, ?_, by group⟩
    exact inv_mem (κ c).2
  refine ⟨fun _ =>
    { lev :=
        { K.lev with
          Uloc_hyp := fun v hv hT => K.lev.Uloc_hyp v (fun h => hv (Or.inl h)) hT
          chi_triv := fun x hx => K.lev.chi_triv x (fun v hv => hx v (Or.inl hv)) }
      y := fun c' => K.y (e.symm c'.1) * κU (e.symm c'.1)
      y_bij := ?_
      y_lat := ?_
      stabI := fun c' => (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'.1).codRestrict _ (hmem c'.1)
      stabI_inj := fun c' s t h => MemChart.stM_inj (Chart0.lvG I a) (Chart0.lvQ I a) _ _ ((l.ch u a).step 0) c'.1 (congrArg Subtype.val h)
      stabI_range := ?_ }, rfl, rfl, rfl, fun x x' h => ?_, fun c => ?_, fun c s => rfl⟩
  · convert K.y_bij.comp (e.symm.bijective.comp
        (Equiv.subtypeUnivEquiv (p := fun c' : (I.stp u a 0).Cl => (fun _ => ()) c' = ()) (fun _ => rfl)).bijective) using 1
    funext c'
    exact hcls (e.symm c'.1)
  · intro c' x
    rw [hlat c'.1]
    refine (K.y_lat (e.symm c'.1) x).trans ?_
    show _ ↔ ((((K.y (e.symm c'.1)).1 * (κ (e.symm c'.1)).1)⁻¹).1 *ᵥ x ∈ _)
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (inv_mem (hL _)).2 _
  · intro c' γ
    have h1 : γ ∈ ((MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'.1).codRestrict _ (hmem c'.1)).range ↔
        γ.1 ∈ (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'.1).range :=
      ⟨fun ⟨s, hs⟩ => ⟨s, congrArg Subtype.val hs⟩, fun ⟨s, hs⟩ => ⟨s, Subtype.ext hs⟩⟩
    refine h1.trans ((hrng c'.1 γ.1).trans (Iff.trans ?_ ((K.stabI_range (e.symm c'.1) γ).trans ?_)))
    · exact ⟨fun ⟨t, ht⟩ => ⟨t, Subtype.ext ((hK _ t).trans ht)⟩, fun ⟨t, ht⟩ => ⟨t, (hK _ t).symm.trans (congrArg Subtype.val ht)⟩⟩
    show _ ↔ _ ∈ K.lev.U.map (MulAut.conj ((K.y (e.symm c'.1)).1 * (κ (e.symm c'.1)).1)).toMonoidHom
    rw [map_conj_mul _ _ _ (κ _).2]
  · show K.lev.chi x = K.lev.chi x'
    exact congrArg K.lev.chi (Subtype.ext h)
  · show (K.y (e.symm (e c))).1 * (κ (e.symm (e c))).1 = _
    rw [e.symm_apply_apply]

end GlobalTheory.TwU.AtTrue.ZeroChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroFormIdentificationRefTupleEqId
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

theorem stepZeroFormIdentification_refTuple_eq_id : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), (I.tw l l0 Z).e0 u (I.rec7 l Z).what₂.mu0 = (I.tw l l0 Z).eMu0 u 0 (Nat.zero_le _) := by
  intro B X I _ _ l Z l0 u
  apply LinearEquiv.ext
  intro x
  have h := (l0 u I.mu0).choose_spec.2 x
  rw [stepZeroTwist_reference_tuple_eq_id l u] at h
  exact (I.fm l u I.mu0).emb_inj 0 h

end GlobalTheory.TwU.AtTrue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelCharacterEqReferenceTuple
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.StepZeroChr

theorem isPtOf_of_deco {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q' = ∅)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {p' : DecoF E n ST SG Q'} (e : p'.deco = p.deco)
    (h : IsPtOf hc g p) : IsPtOf hc g p' :=
  ⟨h.uni, e ▸ h.lat, e ▸ h.f, e ▸ h.be, fun P => (Finset.eq_empty_iff_forall_notMem.1 hQ P.1 P.2).elim⟩

set_option maxHeartbeats 1000000 in

theorem chr_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → chi κ0 = 1 → ∀ (x : U) (κ : (I.stp u a 0).G c'.1), (I.stp u a 0).gam c'.1 κ = 1 → PtOf (y c * κ0.1 * x.1 * k) ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 → ((chi x : ℂˣ) : ℂ) = B.embLL (((I.stp u a 0).chr c'.1 κ : B.LLˣ) : B.LL) := by
  intro B X I hI hP l Z u a Lb U chi y st k hR c κ0 c' hc' _ hchi x κ hκ hpt
  have hd : ((I.stp u a 0).rep c').1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
    subst hc'
    exact ClsZero.stepZero_corresponding_representatives_same_deco hI u a _ c
  have hΛ := ClsZero.levelTypePrimes_stepZero_eq_colLev hI a c'.1
  have hΛ0 := ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 c.1
  have hm : κ.2.1.1 ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).grp := by
    rw [hΛ0, ← hΛ]
    exact κ.2.1.2
  let κ' : (I.stp u I.mu0 0).G c.1 := (κ.1, ⟨κ.2.1.1, hm⟩, 1)
  have e1 : ((I.stp u I.mu0 0).act c.1 κ' ((I.stp u I.mu0 0).rep c)).1.1.deco =
      ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1.deco := by
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) •
      ((I.stp u I.mu0 0).rep c).1.1.deco = ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) •
      ((I.stp u a 0).rep c').1.1.deco
    rw [hd]
  have h1 : PtOf (y c * (κ0 * x).1 * k) ((I.stp u I.mu0 0).act c.1 κ' ((I.stp u I.mu0 0).rep c)).1.1 := by
    rw [Subgroup.coe_mul, ← mul_assoc]
    exact isPtOf_of_deco (RefTup.twistPrimes_reference_tuple_eq_empty B X I) e1 hpt
  have h2 := hR.chr c (κ0 * x) κ' hκ h1
  rw [map_mul, hchi, one_mul] at h2
  refine h2.trans ?_
  congr 2
  show (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr ⟨κ.2.1.1, hm⟩ *
      (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr 1 =
    (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 c'.1).chr κ.2.1 * (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 c'.1).chr κ.2.2
  rw [map_one, StepZero.chr_eq_one (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a c'.1), StepZero.chr_congr hΛ, StepZero.chr_congr hΛ0]

end GlobalTheory.TwU.StepZeroChr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelReadAsReference
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.LevZero

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem moves_iff (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl)
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) :
    (∃ κ : (I.stp u a 0).G c.1, (I.stp u a 0).gam c.1 κ = 1 ∧ ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1 = q ∧
        cosetIn ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)) = cosetIn ((I.stp u a 0).rep c)) ↔
      ∃ g : FormG (colLev I.Ch 0), ufGL B.fields.E (B.R.N 0) g.1 = 1 ∧ g • ((I.stp u a 0).rep c).1.1.deco = q.deco := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  constructor
  · rintro ⟨κ, h1, h2, -⟩
    refine ⟨StepZero.down (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := Chart0.lvQ I a) ((I.Tp a).pref u 0) hΛ c.1 κ, h1, ?_⟩
    exact (StepZero.deco_smul (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := Chart0.lvQ I a) _ hΛ c.1 κ _).symm.trans
      (congrArg (fun q => q.deco) h2)
  · rintro ⟨g₀, h0, hg⟩
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, h2, h3⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p g₀ (by rw [hp]; exact hg)
    refine ⟨g, ?_, ?_, Chart0.cos0 I _ _⟩
    · exact (congrArg (fun g => ufGL B.fields.E (B.R.N 0) g.1) h2).trans h0
    · exact (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp

theorem lev_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → ∀ (x : GA B (B.R.N 0)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0), PtOf (y c * κ0.1 * x * k) q → (x ∈ U ↔ ∃ κ : (I.stp u a 0).G c'.1, (I.stp u a 0).gam c'.1 κ = 1 ∧ ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 = q ∧ cosetIn ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')) = cosetIn ((I.stp u a 0).rep c')) := by
  intro B X I hI _ l _ u a Lb U chi y st k hR c κ0 c' hc' _ x q hq
  have hQ : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  have hq0 : PtOf (y c * (κ0.1 * x) * k) (extTo (I.Q I.mu0) q) := by
    rw [← mul_assoc]
    exact IsPtOf.extTo (hQ ▸ Finset.empty_subset _) (hQ ▸ Finset.disjoint_empty_right _) hq
  have h1 := hR.lev c (κ0.1 * x) (extTo (I.Q I.mu0) q) hq0
  have e : ((I.stp u a 0).rep c').1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
    rw [hc']
    exact ClsZero.stepZero_corresponding_representatives_same_deco hI u a _ c
  refine (Subgroup.mul_mem_cancel_left U κ0.2).symm.trans (h1.trans ((moves_iff I hI u I.mu0 c _).trans ?_))
  refine Iff.trans ?_ (moves_iff I hI u a c' q).symm
  rw [e]
  rfl

end GlobalTheory.Mem.Col2.TC.LevZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroTrivialStabilisersTrueColumnsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stab0_rec7_of_levelData : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), LevelData (I.rec7 l Z) → OrbitPlaces.Stab0 (I.rec7 l Z) := by
  first | exact @GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns | exact GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns | (intros; apply GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticesTwoClassesAdmissibleStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedLattices_two_classes_admissible : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) u μ i j c c', TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N j c')) := by
  first | exact @GlobalTheory.TwV.adm_seam_lat_rd_pair | exact GlobalTheory.TwV.adm_seam_lat_rd_pair | (intros; apply GlobalTheory.TwV.adm_seam_lat_rd_pair <;> assumption)
end

