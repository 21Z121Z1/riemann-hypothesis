import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0078

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarRowsLevelCharacterEqLiftsLevelCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.ChiStarLev

variable {D : D7}

section Level

variable {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levChi_flag' (hs : L.s = 0) (hQ : L.Q = ∅) (κ : GA D V) : levChi V β (flagL L) κ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2]
  simp [flagL, withP, hs, hQ]

theorem levChi_withP' (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) (κ : GA D V) :
    levChi V β (withP L P) κ = ((ext1 P.H P.chi (rTup β L (finE V κ)) : ℂˣ) : ℂ) := by
  have h := levChi_flag' (β := β) hs hQ κ
  unfold levChi at h ⊢
  rw [levFn_withP, Units.val_mul, h, mul_one]

end Level

theorem ext_by_one_apply_of_not_mem_subgroup {G N : Type} [Group G] [One N] [Mul N] {P : Subgroup G} (f : P → N) {x : G} (h : x ∉ P) :
    ext1 P f x = 1 := by
  unfold ext1; rw [dif_neg h]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem star_levChi_levR (R : RealDat D A Ks) (F : Face D A) (b : Bool) (g : GA D (Yc D 0)) :
    star (levChi _ (R.βY 0) (R.dat0 (R.levR F b)) g) = levChi _ (R.βY 0) (R.dat0 (R.levL F b (sg0 D A))) g := by
  have hsg : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  rw [hsg]
  have h1 := levChi_withP' (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levL F b D.what₂.embLL) g
  have h2 := levChi_withP' (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levR F b) g
  have hH : (R.levL F b D.what₂.embLL).H = (R.levR F b).H := rfl
  by_cases hm : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) g) ∈ (R.levR F b).H
  · replace h2 := h2.trans (congrArg Units.val (extendOne_of_mem (P := (R.levR F b).H) (R.levR F b).chi hm))
    replace h1 := h1.trans (congrArg Units.val (extendOne_of_mem (P := (R.levL F b D.what₂.embLL).H) (R.levL F b D.what₂.embLL).chi hm))
    refine Eq.trans (congrArg star h2) (Eq.trans ?_ h1.symm)
    have h3 : (R.levL F b D.what₂.embLL).chi ⟨_, hm⟩ = ((R.levR F b).chi ⟨_, hm⟩)⁻¹ := by
      exact map_inv (Units.map D.what₂.embLL.toMonoidHom) _
    have h4 : IsOfFinOrder ((R.levR F b).chi ⟨_, hm⟩) := by
      have : Finite (G0 R.Pg D.R.r) := Finite.of_equiv _ R.eG.toEquiv
      exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    have h5 : ‖(((R.levR F b).chi ⟨_, hm⟩ : ℂˣ) : ℂ)‖ = 1 := ((Units.coeHom ℂ).isOfFinOrder h4).norm_eq_one
    rw [h3, Units.val_inv_eq_inv_val, Complex.inv_eq_conj h5]
    rfl
  · have hm' : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) g) ∉ (R.levL F b D.what₂.embLL).H := hm
    replace h2 := h2.trans (congrArg Units.val (ext_by_one_apply_of_not_mem_subgroup (P := (R.levR F b).H) (R.levR F b).chi hm))
    replace h1 := h1.trans (congrArg Units.val (ext_by_one_apply_of_not_mem_subgroup (P := (R.levL F b D.what₂.embLL).H) (R.levL F b D.what₂.embLL).chi hm'))
    refine Eq.trans (congrArg star h2) (Eq.trans ?_ h1.symm)
    simp

end GlobalTheory.ChiStarLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SylvesterInertiaInvariance
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.SigCong

theorem card_pos_le_of_conj {n : ℕ} (A B X : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hX : Xᴴ * A * X = B) :
    Fintype.card {i : Fin n // 0 < hB.eigenvalues i} ≤ Fintype.card {i : Fin n // 0 < hA.eigenvalues i} := by
  set φ : ({i // 0 < hB.eigenvalues i} → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    Matrix.mulVecLin X ∘ₗ Matrix.mulVecLin (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ∘ₗ
      GlobalTheory.SimSign.extZero (fun i => 0 < hB.eigenvalues i) with hφ
  have hq : ∀ w, w ≠ 0 → 0 < (star (φ w) ⬝ᵥ A *ᵥ φ w).re := fun w hw => by
    simp only [hφ, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply]
    rw [GlobalTheory.SimSign.quad_mulVec, hX, GlobalTheory.SimSign.re_quad_ext]
    exact GlobalTheory.SimSign.sum_pos B hB w hw
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have := hq w hne
    rw [hw] at this
    simp at this
  have hS : ∀ u ∈ LinearMap.range φ, u ≠ 0 → 0 < (star u ⬝ᵥ A *ᵥ u).re := by
    rintro u ⟨w, rfl⟩ hu
    exact hq w (fun h0 => hu (by rw [h0, map_zero]))
  have h1 := GlobalTheory.SimSign.finrank_le_pos A hA _ hS
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card] at h1
  exact h1

theorem sigPosH_congr : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 →
    ∀ (Z : GL (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.IsHermitian),
      B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) → sigPosH hB = sigPosH hA := by
  intro n A hA _ Z B hB hBZ
  unfold sigPosH
  refine le_antisymm (card_pos_le_of_conj A B _ hA hB hBZ.symm)
    (card_pos_le_of_conj B A ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) hB hA ?_)
  have h1 : (Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.mul_inv Z
  rw [hBZ]
  calc (((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᴴ * ((Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A *
        (Z : Matrix (Fin n) (Fin n) ℂ)) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      = ((Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᴴ * A *
        ((Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = A := by rw [h1]; simp

end GlobalTheory.SigCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymNegTSwap
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem isGl_negT {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (F : ι → ι → Module.End ℂ M) (h : IsGl F) : IsGl (negT F) := by
  intro a b c d
  have h1 := h d c b a
  simp only [negT, neg_mul_neg]
  have e1 : F b a * F d c - F d c * F b a = -(F d c * F b a - F b a * F d c) := by abel
  rw [e1, h1]
  simp only [@eq_comm _ c b, @eq_comm _ a d]
  split_ifs <;> abel

theorem unitOn_negT {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (h : UnitOn s F U) :
    UnitOn s (negT F) U := by
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := h
  refine ⟨hfd, fun a b hab u hu => ?_, ip, hsym, hpos, fun a b hab x hx y hy => ?_⟩
  · simp only [negT, LinearMap.neg_apply]
    exact U.neg_mem (hst b a hab.symm u hu)
  · simp only [negT, LinearMap.neg_apply, map_neg, LinearMap.neg_apply]
    rw [hadj b a hab.symm x hx y hy]

theorem unitOn_not {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (h : UnitOn s F U) :
    UnitOn (fun a => !s a) F U := by
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := h
  refine ⟨hfd, fun a b hab u hu => hst a b (by simpa using hab) u hu, ip, hsym, hpos,
    fun a b hab x hx y hy => hadj a b (by simpa using hab) x hx y hy⟩

theorem sym_negT_swap : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), (IsGl F → IsGl (negT F)) ∧ cas s (negT F) = cas s F ∧ cas (fun a => !s a) F = cas s F ∧ (∀ U, UnitOn s F U → UnitOn s (negT F) U ∧ UnitOn (fun a => !s a) F U) ∧ (LocU s F → LocU s (negT F) ∧ LocU (fun a => !s a) F) := by
  intro ι M _ _ _ _ s F
  refine ⟨isGl_negT F, ?_, ?_, fun U hU => ⟨unitOn_negT s F U hU, unitOn_not s F U hU⟩, fun h => ⟨?_, ?_⟩⟩
  · unfold cas negT
    simp only [neg_mul_neg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [eq_comm]
  · unfold cas
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Bool.not_inj_iff]
  · intro t
    obtain ⟨U, hU, hUn⟩ := h t
    exact ⟨U, hU, unitOn_negT s F U hUn⟩
  · intro t
    obtain ⟨U, hU, hUn⟩ := h t
    exact ⟨U, hU, unitOn_not s F U hUn⟩

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionIsLieAction
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult.TLie

variable {R S : ℕ}

lemma adCoeff_eq (Z : Mat R S) (y x : NC R S) :
    adP Z y x = (Z * eNC x - eNC x * Z) y.1.1 y.1.2 := by
  obtain ⟨⟨a, b⟩, h⟩ := y
  obtain ⟨⟨c, d⟩, h'⟩ := x
  simp only [adP, eNC, Eab, Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply]
  congr 1
  · rw [Finset.sum_eq_single c]
    · by_cases hbd : b = d
      · simp [hbd]
      · simp [hbd, Ne.symm hbd]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · rw [Finset.sum_eq_single d]
    · by_cases hac : a = c
      · simp [hac]
      · simp [hac, Ne.symm hac]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp

lemma same_trans {a b c : Ix R S} (h1 : sameBlock a b) (h2 : sameBlock b c) : sameBlock a c := by
  cases a <;> cases b <;> cases c <;> first | trivial | exact h1.elim | exact h2.elim

lemma sum_NC (f : Ix R S × Ix R S → ℂ) (hf : ∀ p, sameBlock p.1 p.2 → f p = 0) :
    ∑ x : NC R S, f x.1 = ∑ p, f p := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Ix R S × Ix R S => ¬ sameBlock p.1 p.2)
    (fun p => by rw [Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)) f]
  exact Finset.sum_filter_of_ne fun p _ hp hs => hp (hf p hs)

lemma sum_all {ι : Type} [Fintype ι] [DecidableEq ι] (Y M : Matrix ι ι ℂ) (a b : ι) :
    ∑ p : ι × ι, (Y a p.1 * (if b = p.2 then 1 else 0) - (if a = p.1 then 1 else 0) * Y p.2 b) * M p.1 p.2 =
      (Y * M - M * Y) a b := by
  rw [Fintype.sum_prod_type]
  simp only [sub_mul, Finset.sum_sub_distrib, Matrix.sub_apply, Matrix.mul_apply]
  congr 1
  · simp
  · rw [Finset.sum_comm]
    simp [mul_comm]

lemma sum_adP {Y : Mat R S} (hY : IsKC Y) (M : Mat R S) (y : NC R S) :
    ∑ x : NC R S, adP Y y x * M x.1.1 x.1.2 = (Y * M - M * Y) y.1.1 y.1.2 := by
  obtain ⟨⟨a, b⟩, h⟩ := y
  refine Eq.trans ?_ (sum_all Y M a b)
  refine sum_NC (fun p =>
    (Y a p.1 * (if b = p.2 then 1 else 0) - (if a = p.1 then 1 else 0) * Y p.2 b) * M p.1 p.2) ?_
  rintro ⟨c, d⟩ hs
  have e1 : Y a c * (if b = d then 1 else 0) = 0 := by
    split_ifs with hbd
    · subst hbd
      rw [hY a c (fun hac => h (same_trans hac hs)), zero_mul]
    · exact mul_zero _
  have e2 : (if a = c then 1 else 0) * Y d b = 0 := by
    split_ifs with hac
    · subst hac
      rw [hY d b (fun hdb => h (same_trans hs hdb)), mul_zero]
    · exact zero_mul _
  simp only [e1, e2, sub_zero, zero_mul]

lemma adCoeff_commutator {Y Z : Mat R S} (hY : IsKC Y) (hZ : IsKC Z) (y w : NC R S) :
    adP (Y * Z - Z * Y) y w = ∑ x, adP Y y x * adP Z x w - ∑ x, adP Z y x * adP Y x w := by
  have h1 := sum_adP hY (Z * eNC w - eNC w * Z) y
  have h2 := sum_adP hZ (Y * eNC w - eNC w * Y) y
  simp only [← adCoeff_eq] at h1 h2
  rw [h1, h2, adCoeff_eq, ← Matrix.sub_apply]
  refine congrFun (congrFun ?_ _) _
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

variable {W : Type} [AddCommGroup W] [Module ℂ W]

lemma factorOp_apply (k : ℕ) (i : Fin k) (Z : Mat R S) (Ψ : (Fin k → NC R S) → W) (g : Fin k → NC R S) :
    factorOp k i Z Ψ g = ∑ x, adP Z (g i) x • Ψ (Function.update g i x) := rfl

lemma factorOp_commutator (k : ℕ) (i : Fin k) {Y Z : Mat R S} (hY : IsKC Y) (hZ : IsKC Z) :
    (factorOp k i (Y * Z - Z * Y) : Module.End ℂ ((Fin k → NC R S) → W)) =
      factorOp k i Y * factorOp k i Z - factorOp k i Z * factorOp k i Y := by
  refine LinearMap.ext fun Ψ => funext fun g => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, factorOp_apply,
    Function.update_self, Function.update_idem, adCoeff_commutator hY hZ, sub_smul, Finset.sum_sub_distrib,
    Finset.sum_smul, Finset.smul_sum, mul_smul]
  congr 1 <;> exact Finset.sum_comm

lemma factorOp_comm_of_ne (k : ℕ) {i j : Fin k} (hij : i ≠ j) (Y Z : Mat R S) :
    (factorOp k i Y * factorOp k j Z : Module.End ℂ ((Fin k → NC R S) → W)) =
      factorOp k j Z * factorOp k i Y := by
  refine LinearMap.ext fun Ψ => funext fun g => ?_
  simp only [Module.End.mul_apply, factorOp_apply, Function.update_of_ne hij,
    Function.update_of_ne hij.symm, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_comm, Function.update_comm hij]

def ptOp (k : ℕ) (A : Module.End ℂ W) : Module.End ℂ ((Fin k → NC R S) → W) :=
  LinearMap.pi (fun g => A ∘ₗ LinearMap.proj g)

lemma ptOp_comm_factorOp (k : ℕ) (i : Fin k) (A : Module.End ℂ W) (Z : Mat R S) :
    (ptOp k A * factorOp k i Z : Module.End ℂ ((Fin k → NC R S) → W)) = factorOp k i Z * ptOp k A := by
  refine LinearMap.ext fun Ψ => funext fun g => ?_
  simp [ptOp, factorOp_apply]

lemma tAct_eq (k : ℕ) (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Z : Mat R S) :
    tAct k actW Z = ptOp k (actW Z) + ∑ i, factorOp k i Z := rfl

theorem isKLieAct_tAct (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (h : IsKLieAct actW) : IsKLieAct (tAct k actW) := by
  intro Y Z hY hZ
  have hp : (ptOp k (actW (Y * Z - Z * Y)) : Module.End ℂ ((Fin k → NC R S) → W)) =
      ptOp k (actW Y) * ptOp k (actW Z) - ptOp k (actW Z) * ptOp k (actW Y) := by
    rw [h Y Z hY hZ]
    refine LinearMap.ext fun Ψ => funext fun g => ?_
    simp [ptOp]
  have hs : (∑ i, factorOp k i (Y * Z - Z * Y) : Module.End ℂ ((Fin k → NC R S) → W)) =
      (∑ i, factorOp k i Y) * (∑ i, factorOp k i Z) - (∑ i, factorOp k i Z) * (∑ i, factorOp k i Y) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_comm (f := fun i j => (factorOp k i Z * factorOp k j Y :
        Module.End ℂ ((Fin k → NC R S) → W))), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i, factorOp_commutator k i hY hZ]
    · intro j _ hj
      rw [factorOp_comm_of_ne k hj.symm, sub_self]
    · simp
  have hc : ∀ (A : Module.End ℂ W) (X : Mat R S),
      (ptOp k A * (∑ i, factorOp k i X) : Module.End ℂ ((Fin k → NC R S) → W)) =
        (∑ i, factorOp k i X) * ptOp k A := by
    intro A X
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => ptOp_comm_factorOp k i A X
  rw [tAct_eq, tAct_eq, tAct_eq, hp, hs]
  simp only [add_mul, mul_add, hc]
  abel

end GlobalTheory.SteepMult.TLie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionWeightDecomposition
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

lemma adP_Eab_self {R S : ℕ} (c : Ix R S) (y x : NC R S) :
    adP (Eab c c) y x = if x = y then ((if y.1.1 = c then 1 else 0) - (if y.1.2 = c then 1 else 0) : ℂ) else 0 := by
  obtain ⟨⟨a, b⟩, h⟩ := x
  obtain ⟨⟨a', b'⟩, h'⟩ := y
  simp only [adP, Eab, Matrix.single_apply, Subtype.mk.injEq, Prod.mk.injEq]
  by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> by_cases h3 : c = a' <;> by_cases h4 : c = b' <;>
    simp_all [eq_comm] <;> grind

lemma tAct_Eab_self_apply {R S k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (c : Ix R S) (Ψ : (Fin k → NC R S) → W) (g : Fin k → NC R S) :
    tAct k actW (Eab c c) Ψ g = actW (Eab c c) (Ψ g) +
      (∑ i, ((if (g i).1.1 = c then 1 else 0) - (if (g i).1.2 = c then 1 else 0) : ℂ)) • Ψ g := by
  rw [tAct_apply, Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (g i)]
  · simp [adP_Eab_self]
  · intro x _ hx
    simp [adP_Eab_self, hx]
  · simp

lemma single_mem_wtSub {R S k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (g : Fin k → NC R S) (μ : Ix R S → ℚ) (w : W) (hw : w ∈ wtSub actW μ) :
    (Pi.single g w : (Fin k → NC R S) → W) ∈ wtSub (tAct k actW)
      (fun c => μ c + ∑ i, ((if (g i).1.1 = c then 1 else 0) - (if (g i).1.2 = c then 1 else 0))) := by
  rw [GlobalTheory.TensorHW.mem_wt] at hw ⊢
  intro c
  funext h
  rw [tAct_Eab_self_apply]
  by_cases hh : h = g
  · subst hh
    simp only [Pi.single_eq_same, Pi.smul_apply, hw c, ← add_smul]
    congr 1
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  · simp [hh]

theorem tAct_mem_iSup_wtSub (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (hW : ∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ)
    (Ψ : (Fin k → NC R S) → W) : Ψ ∈ ⨆ μ : Ix R S → ℚ, wtSub (tAct k actW) μ := by
  rw [← Finset.univ_sum_single Ψ]
  refine Submodule.sum_mem _ fun g _ => ?_
  refine Submodule.iSup_induction (motive := fun w => (Pi.single g w : (Fin k → NC R S) → W) ∈
    ⨆ μ : Ix R S → ℚ, wtSub (tAct k actW) μ) _ (hW (Ψ g)) ?_ ?_ ?_
  · intro μ w hw
    exact Submodule.mem_iSup_of_mem _ (single_mem_wtSub actW g μ w hw)
  · simp
  · intro x y hx hy
    rw [Pi.single_add]
    exact Submodule.add_mem _ hx hy

end GlobalTheory.SteepMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFixedFieldEmbeddingInjective
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc.BaseChangeCent

variable {p : ℕ} [Fact p.Prime]

def shL (G : HTGroup p) : G.C →ₗ[ℚ] G.C where
  toFun := sh G
  map_add' x y := by simp only [sh, map_add, MulOpposite.unop_add]
  map_smul' q x := by
    show (G.star (q • x)).unop = q • (G.star x).unop
    rw [map_rat_smul]; rfl

theorem shL_apply (G : HTGroup p) (c : G.C) : shL G c = sh G c := rfl

def phi (G : HTGroup p) (β Y : G.C) (β' : G.C) : G.C →ₗ[ℚ] G.C × G.C :=
  (LinearMap.mulRight ℚ Y - LinearMap.mulLeft ℚ Y).prod
    (LinearMap.mulLeft ℚ β ∘ₗ LinearMap.mulRight ℚ β' ∘ₗ shL G - LinearMap.id)

theorem phi_apply (G : HTGroup p) (β Y β' c : G.C) :
    phi G β Y β' c = (c * Y - Y * c, β * sh G c * β' - c) := by
  simp [phi, shL_apply, mul_assoc]

theorem lTensor_phi (G : HTGroup p) (K : Type) [Field K] [Algebra ℚ K] (β Y β' : G.C)
    (x : K ⊗[ℚ] G.C) :
    TensorProduct.prodRight ℚ ℚ K G.C G.C ((phi G β Y β').lTensor K x) =
      (x * inC G K Y - inC G K Y * x, inC G K β * (starT G.star K x).unop * inC G K β' - x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp <;> rfl
  | tmul k c =>
    simp only [LinearMap.lTensor_tmul, phi_apply, TensorProduct.prodRight_tmul, inC, starT_tmul,
      AlgHom.coe_toRingHom, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.tmul_sub, sh]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    simp only [map_add, MulOpposite.unop_add, mul_add, add_mul, Prod.mk_add_mk]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> abel

end GlobalTheory.FinClsLoc.BaseChangeCent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamily
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow

theorem weightSizes_along : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x →
    ∀ (i : Fm.Ix x) j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨x0, fun x hx1 hx i j => ?_⟩
  obtain ⟨-, -, -, heta, hw, h4, h2b, -, hw1, hsum⟩ := h0 x hx hx1 i
  have SZ := Fm.sizes x hx1 i
  have P := Fm.params x hx1 i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩ := SZ
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have he := L.etaSz_pos
  have hSc := L.Sc_pos
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'.le (by linarith)
  have hq0 : 0 < L.sc.b' / L.sc.x := div_pos hb' hxp
  have hwj : ∀ τ, wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    intro τ
    unfold wj
    rw [dif_pos (by omega)]
    rfl
  have hwin : ∀ τ, 0 < wj D (j.1 + 1) τ ∧ wj D (j.1 + 1) τ ≤ 2 * L.sc.b := by
    intro τ
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have := L.win_thick (j.1 + 1) (by omega) (by omega) τ h1
      constructor <;> linarith [this.1, this.2]
    by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have a := L.win_top (j.1 + 1) (by omega) (by omega) τ ⟨t, ht⟩ e.symm
      have a3 := L.bT_ge ⟨t, ht⟩
      have a4 := GlobalTheory.Ggeo.bT_le_five_quarters P ⟨t, ht⟩
      constructor <;> linarith [a.1, a.2]
    · have a := L.win_thin (j.1 + 1) (by omega) (by omega) τ ⟨(D.eTau τ).2, h2, h1⟩
      constructor <;> linarith [a.1, a.2]
  refine ⟨fun τ => ⟨?_, ?_, fun l => ?_, fun l => ?_⟩, fun l => (hG l l).1⟩
  · rw [← hwj]; exact (hwin τ).1
  · rw [← hwj]; exact (hwin τ).2
  · have := L.cloud_v τ l
    exact ⟨this.1, by linarith [this.2]⟩
  · have := L.be_close τ l j
    push_cast at this
    linarith

end GlobalTheory.LowRow
end
end

