import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0202
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0226
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0212
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntegralSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightNonnegOfIdempotentGlnPr
section
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace CompanionTheory.Member.TraceCoefficientSum

variable {G : Type} [Group G] [Fintype G]

theorem coeff_zOf (χ : G → ℂ) (x : G) : (zOf χ).coeff x = χ 1 / (Fintype.card G : ℂ) * χ x⁻¹ := by
  simp [zOf, MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem eq_sum_single (a : MonoidAlgebra ℂ G) : a = ∑ x, MonoidAlgebra.single x (a.coeff x) := by
  ext y
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem coeff_mul_zOf (a : MonoidAlgebra ℂ G) (χ : G → ℂ) :
    (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * ∑ x, a.coeff x * χ x := by
  conv_lhs => rw [eq_sum_single a]
  rw [Finset.sum_mul, MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MonoidAlgebra.coeff_single_mul_apply, coeff_zOf, mul_one, inv_inv]
  ring

theorem trace_alg (a : MonoidAlgebra ℂ G) (V : FDRep ℂ G) :
    ∑ x, a.coeff x * V.character x =
      LinearMap.trace ℂ V (Representation.asAlgebraHom (V.ρ : Representation ℂ G V) a) := by
  conv_rhs => rw [eq_sum_single a]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul]
  rfl

theorem trace_nat (a : MonoidAlgebra ℂ G) (ha : a * a = a) (V : FDRep ℂ G) :
    ∃ m : ℕ, ∑ x, a.coeff x * V.character x = m := by
  have hi : IsIdempotentElem (Representation.asAlgebraHom (V.ρ : Representation ℂ G V) a) := by
    unfold IsIdempotentElem
    rw [← map_mul, ha]
  rw [trace_alg]
  exact ⟨_, (LinearMap.IsIdempotentElem.isProj_range _ hi).trace⟩

theorem re_nonneg (a : MonoidAlgebra ℂ G) (ha : a * a = a) (χ : G → ℂ) (hχ : IsIrr χ) :
    0 ≤ ((a * zOf χ).coeff 1).re := by
  obtain ⟨V, -, hV⟩ := hχ
  obtain ⟨m, hm⟩ := trace_nat a ha V
  rw [coeff_mul_zOf, ← hV 1, FDRep.char_one]
  simp only [← hV]
  rw [hm, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast m,
    ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

end CompanionTheory.Member.TraceCoefficientSum

theorem CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  intro g _ L n a ha h1 f
  refine div_nonneg ?_ h1
  unfold eSerC
  refine finsum_mem_induction (fun b => 0 ≤ ((a * b).coeff 1).re) (by simp) ?_ ?_
  · intro x y hx hy
    rw [mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, Complex.add_re]
    exact add_nonneg hx hy
  · intro χ hχ
    exact CompanionTheory.Member.TraceCoefficientSum.re_nonneg a ha χ hχ.1

end

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
theorem _root_.GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  first | exact @CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent | exact CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent | (intros; apply CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateBasisOfIsDecompletionAtLevel
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem htBasis_of_isDec : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m d : ℕ) (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (J : Set ℤ), IsDec act χ K m M Dm U g → HTBasis act χ (Gj K m) M J → HTBasis act χ (Gj K m) U J := by
  intro l _ act χ _ _ K m d M U Dm g J hD hH
  obtain ⟨hdet, -, -, -, hrel⟩ := hD
  obtain ⟨e, u, hli, hu, hfix⟩ := hH
  have hDe : ∀ v : Fin d → PadicComplex l, Dm.mulVec (Dm⁻¹.mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hinj : ∀ v w : Fin d → PadicComplex l, Dm.mulVec v = Dm.mulVec w → v = w := by
    intro v w h
    have h2 := congrArg (fun x => Dm⁻¹.mulVec x) h
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] using h2
  refine ⟨fun k => Dm⁻¹.mulVec (e k), u, ?_, hu, ?_⟩
  · refine LinearIndependent.of_comp Dm.mulVecLin ?_
    have : (Dm.mulVecLin ∘ fun k => Dm⁻¹.mulVec (e k)) = e := by
      funext k
      exact hDe (e k)
    rw [this]
    exact hli
  · intro σ hσ k
    apply hinj
    have hmap : (Dm.map (act σ)).mulVec (fun a => act σ (Dm⁻¹.mulVec (e k) a)) =
        fun a => act σ (e k a) := by
      funext a
      conv_rhs => rw [← hDe (e k)]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    have h1 := hfix σ hσ k
    unfold twAct at h1 ⊢
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hrel σ hσ, ← Matrix.mulVec_mulVec, hmap, h1, hDe]

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HomToCharacterLineEqZero
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models

theorem ModTh.abc_Nχ_of_range {k G : Type} [Field k] [Group G] {l n : ℕ} {R : RingPG k l} {F : DFun R n G}
    {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (e : ℤ) (h1 : -1 ≤ e) (h2 : e < Dt.t) :
    ABC (F.D (chr (M.ω ^ (-e)))) Dt.w Dt.wst (M.Nχ e) := by
  refine ⟨fun i => (M.χ_lat e h1 h2 i).1, fun i => ?_, fun i => (M.χ_lat e h1 h2 i).2.1⟩
  have ht : (1 : ℤ) ≤ Dt.t := by exact_mod_cast Dt.one_le_letterBlockLength
  have a := Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩)))
  have b := Dt.range i (Dt.w i + Dt.t - 1) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))
  rw [(M.χ_lat e h1 h2 i).2.2.1]
  exact ⟨sh_le_sh_of_le (by omega) _, sh_le_sh_of_le (by unfold TopData.wst; omega) _⟩

theorem ModTh.hom_chr_eq_zero : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), -1 ≤ e → e < Dt.t → ∀ (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ (chr (M.ω ^ (-e))) p → p = 0 := by
  intro k G _ _ l n _ _ _ R F r Dt M T1 T2 T3 e h1 h2 A₁ j p hj hinj hp
  by_contra hne
  have hsurj : Function.Surjective p := by
    obtain ⟨x, hx⟩ : ∃ x, p x ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (LinearMap.ext h)
    have hx0 : p x 0 ≠ 0 := fun h => hx (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
    intro y
    refine ⟨(y 0 / p x 0) • x, funext fun i => ?_⟩
    rw [Subsingleton.elim i 0, map_smul, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hx0]
  have hT := GlobalTheory.T.obj_and_abc_of_model F M M.T M.Nstd M.std_model
  have hsub := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A₁ M.T j M.Nstd hj hinj M.std_model
  have hq := ModTh.model_push_of_surjective F M A₁ (chr (M.ω ^ (-e))) p _ hp hsurj hsub
  have hN := GlobalTheory.T.obj_and_abc_of_model F M _ _ hq
  have hχ := M.abc_Nχ_of_range e h1 h2
  have hs : sen ((F.D (chr (M.ω ^ (-e)))).γ 0) (M.Nχ e 0) (e : k) ≠ 0 := by
    rw [(M.χ_lat e h1 h2 0).2.2.2]
    classical
    unfold resCount
    rw [Ne, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro h
    exact h e (Multiset.mem_singleton_self e) (by simp)
  obtain ⟨a, ha, hsa⟩ := GlobalTheory.T.senWeights_close_of_height_gamma_conditions (F.D (chr (M.ω ^ (-e)))) Dt _ _ hN.2 hχ 0 (e : k) hs
  have hle := GlobalTheory.T.senMultiplicity_subquotient_lattice_le F M.T A₁ (chr (M.ω ^ (-e))) j p Dt.w Dt.wst M.Nstd hT.1 hj hinj hp hsurj hT.2 0
    ((e : k) + a)
  have hstd : resCount (Dt.U 0) (Dt.w 0) ((e : k) + a) ≠ 0 := by
    rw [← M.std_sen]
    omega
  classical
  unfold resCount at hstd
  rw [Ne, Multiset.card_eq_zero, Multiset.filter_eq_nil] at hstd
  push Not at hstd
  obtain ⟨u, hu, hu'⟩ := hstd
  rw [abs_le] at ha
  refine (GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt T1 T2 T3 0).2.1 u hu (Dt.w 0 + e + a) (by omega) (by omega) ?_
  push_cast at hu' ⊢
  linear_combination hu'

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughOfIsSubFam
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory

theorem subIner_component_mem {L Y I α : Type} [Field L] [AddCommGroup Y] [Module L Y]
    (T : I → Y →ₗ[L] Y) (χ : α → I → L) (hχ : Function.Injective χ) (U : Submodule L Y)
    (hU : ∀ g, ∀ y ∈ U, T g y ∈ U) (S : Finset α) :
    ∀ y : α → Y, (∀ a ∈ S, ∀ g, T g (y a) = χ a g • y a) → ∑ a ∈ S, y a ∈ U → ∀ a ∈ S, y a ∈ U := by
  first
  | exact @_root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem
  | exact _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem
  | (apply _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem ..)

theorem subIner_pullback {L X Y I α J : Type} [Field L] [AddCommGroup X] [Module L X]
    [AddCommGroup Y] [Module L Y] (T : I → X →ₗ[L] X) (T' : J → I → Y →ₗ[L] Y)
    (m : J → X →ₗ[L] Y) (hm : ∀ j g x, m j (T g x) = T' j g (m j x))
    (hinj : ∀ x, (∀ j, m j x = 0) → x = 0)
    (χ : α → I → L) (hχ : Function.Injective χ) (D : Submodule L X)
    (hD : ∀ g, ∀ x ∈ D, T g x ∈ D) (S : Finset α) (d : X) (hd : d ∈ D)
    (y : J → α → Y) (hy : ∀ j, ∀ a ∈ S, ∀ g, T' j g (y j a) = χ a g • y j a)
    (hs : ∀ j, ∑ a ∈ S, y j a = m j d) :
    ∃ x : α → X, (∀ a ∈ S, x a ∈ D ∧ ∀ g, T g (x a) = χ a g • x a) ∧ ∑ a ∈ S, x a = d := by
  classical
  have key := subIner_component_mem (Y := J → Y)
    (fun g => LinearMap.pi fun j => (T' j g).comp (LinearMap.proj j)) χ hχ (D.map (LinearMap.pi m))
    (by
      rintro g _ ⟨x, hx, rfl⟩
      exact ⟨T g x, hD g x hx, by ext j; simp [hm]⟩) S (fun a j => y j a)
    (fun a ha g => by ext j; simp [hy j a ha g])
    ⟨d, hd, by ext j; simp [← hs j, Finset.sum_apply]⟩
  have h1 : ∀ a, ∃ x : X, a ∈ S → x ∈ D ∧ ∀ j, m j x = y j a := by
    intro a
    by_cases ha : a ∈ S
    · obtain ⟨x, hx, e⟩ := key a ha
      exact ⟨x, fun _ => ⟨hx, fun j => congrFun e j⟩⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose x hx using h1
  refine ⟨x, fun a ha => ⟨(hx a ha).1, fun g => ?_⟩, ?_⟩
  · rw [← sub_eq_zero]
    refine hinj _ fun j => ?_
    rw [map_sub, hm, map_smul, (hx a ha).2, hy j a ha, sub_self]
  · rw [← sub_eq_zero]
    refine hinj _ fun j => ?_
    rw [map_sub, map_sum, ← hs j, sub_eq_zero]
    exact Finset.sum_congr rfl fun a ha => (hx a ha).2 j

theorem subIner_rTensor_inj {Qp LL B V U : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    [AddCommGroup B] [Module Qp B]
    [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
    {n : ℕ} (p : Fin n → V →ₗ[LL] U) (hp : ∀ v, (∀ j, p j v = 0) → v = 0) (x : V ⊗[Qp] B)
    (hx : ∀ j, AlgebraTensorModule.rTensor Qp B (p j) x = 0) : x = 0 := by
  obtain ⟨q, hq⟩ := (LinearMap.pi p).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot'.2 fun v hv => hp v fun j => congrFun hv j)
  have h1 : ∀ v, ∑ j, q (Pi.single j (p j v)) = v := by
    intro v
    rw [← map_sum, Finset.univ_sum_single]
    exact LinearMap.congr_fun hq v
  have h2 : ∀ z : V ⊗[Qp] B, ∑ j, AlgebraTensorModule.rTensor Qp B
      (q.comp (LinearMap.single LL (fun _ => U) j)) (AlgebraTensorModule.rTensor Qp B (p j) z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      conv_rhs => rw [← h1 v, TensorProduct.sum_tmul]
      simp
    | add z w hz hw => simp only [map_add, Finset.sum_add_distrib, hz, hw]
  rw [← h2 x]
  simp [hx]

section General

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]

theorem subIner_mem_Dpcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ PC.Dpcris ρ ↔ ∀ h ∈ PC.H, actVB PC.PD ρ h x = x := by
  have h1 : ∀ (h : PC.H) (z : V ⊗[Qp] B), actVB PC.PD' (PC.resH ρ) h z = actVB PC.PD ρ h z := by
    intro h z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, PotCrysData.resH, PC.actB_eq]
    | add z w hz hw => simp only [map_add, hz, hw]
  simp [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, sub_eq_zero, h1]

theorem subIner_actVB_mul (ρ : Representation LL G V) (g h : G) (z : V ⊗[Qp] B) :
    actVB PC.PD ρ g (actVB PC.PD ρ h z) = actVB PC.PD ρ (g * h) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem subIner_Dpcris_stable (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B)
    (hx : x ∈ PC.Dpcris ρ) : actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  rw [subIner_mem_Dpcris] at hx ⊢
  intro h hh
  have h1 := hx (g⁻¹ * h * g⁻¹⁻¹) (PC.normal.conj_mem h hh g⁻¹)
  conv_rhs => rw [← h1]
  rw [subIner_actVB_mul, subIner_actVB_mul]
  congr 2
  group

theorem subIner_rTensor_actVB (ρ : Representation LL G V) (σ : Representation LL G U)
    (f : V →ₗ[LL] U) (hf : ∀ g v, f (ρ g v) = σ g (f v)) (g : G) (z : V ⊗[Qp] B) :
    AlgebraTensorModule.rTensor Qp B f (actVB PC.PD ρ g z) =
      actVB PC.PD σ g (AlgebraTensorModule.rTensor Qp B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hf]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem subIner_mem_Eig (ρ : Representation LL G V) (I : Subgroup G) (a : I →* LLˣ) (x : V ⊗[Qp] B) :
    x ∈ PC.Eig ρ I a ↔ x ∈ PC.Dpcris ρ ∧ ∀ g : I, actVB PC.PD ρ g x = ((a g : LLˣ) : LL) • x := by
  simp [PotCrysData.Eig, Submodule.mem_iInf, sub_eq_zero]

theorem subIner_Dpcris_eq (ρ : Representation LL G V) {n : ℕ} (σ : Fin n → Representation LL G U)
    (p : Fin n → V →ₗ[LL] U) (hp : ∀ j g v, p j (ρ g v) = σ j g (p j v))
    (hinj : ∀ v, (∀ j, p j v = 0) → v = 0) (I : Subgroup G) (Sig : Finset (I →* LLˣ))
    (hσ : ∀ j, PC.Dpcris (σ j) = ⨆ a ∈ Sig, PC.Eig (σ j) I a) :
    PC.Dpcris ρ = ⨆ a ∈ Sig, PC.Eig ρ I a := by
  refine le_antisymm (fun d hd => ?_) (iSup₂_le fun a _ => inf_le_left)
  have h1 : ∀ j, ∃ μ : ∀ a, PC.Eig (σ j) I a,
      ∑ a ∈ Sig, (μ a : U ⊗[Qp] B) = AlgebraTensorModule.rTensor Qp B (p j) d := by
    intro j
    rw [← Submodule.mem_iSup_finset_iff_exists_sum, ← hσ j, subIner_mem_Dpcris]
    intro h hh
    rw [← subIner_rTensor_actVB PC ρ (σ j) (p j) (hp j), (subIner_mem_Dpcris PC ρ d).1 hd h hh]
  choose μ hμ using h1
  obtain ⟨x, hx, rfl⟩ := subIner_pullback (fun g : I => actVB PC.PD ρ g)
    (fun j (g : I) => actVB PC.PD (σ j) g) (fun j => AlgebraTensorModule.rTensor Qp B (p j))
    (fun j g z => subIner_rTensor_actVB PC ρ (σ j) (p j) (hp j) g z)
    (subIner_rTensor_inj p hinj) (fun (a : I →* LLˣ) g => ((a g : LLˣ) : LL))
    (fun a b hab => MonoidHom.ext fun g => Units.ext (congrFun hab g)) (PC.Dpcris ρ)
    (fun g z hz => subIner_Dpcris_stable PC ρ g z hz) Sig d hd (fun j a => μ j a)
    (fun j a _ g => ((subIner_mem_Eig PC (σ j) I a _).1 (μ j a).2).2 g) hμ
  refine Submodule.sum_mem _ fun a ha => ?_
  exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha
    ((subIner_mem_Eig PC ρ I a _).2 (hx a ha)))

end General

theorem inertiaThrough_of_isSubFam : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (ι : Type) (k : ℕ) (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (W : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsSubFam Ms W → ∀ (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)), (∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1) → (∀ a ∈ Sig, Nat.Coprime (orderOf a) (pc P h hN hF hS).PD.p) → (∀ x, (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig) → (pc P h hN hF hS).InertiaThrough W.ρ Sig := by
  intro l _ P K K' LL h hN hF hS ι k Ms W hW Sig h1 h2 h3
  obtain ⟨a, x, p, hp, hinj⟩ := hW
  refine ⟨h1, h2, ?_⟩
  exact subIner_Dpcris_eq (pc P h hN hF hS) W.ρ (fun j => matRep (Ms (x j))) p
    (fun j g v => by rw [hp]; simp [matRep]) hinj _ Sig fun j => (h3 (x j)).2.2

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc

theorem isOpen_of_fg_of_span_eq_top {LL O V : Type} [Field LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    (hO : IsOpen (Set.range (algebraMap O LL))) (M : Submodule O V) (hfg : M.FG)
    (hspan : Submodule.span LL (M : Set V) = ⊤) : IsOpen (M : Set V) := by
  obtain ⟨n, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hbM : ∀ i, b i ∈ M := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  have hsurj : Function.Surjective (Fintype.linearCombination LL b) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, ← hspan, ← hb,
      Submodule.span_span_of_tower]
  have hopen : IsOpenMap (Fintype.linearCombination LL b) :=
    IsModuleTopology.isOpenMap_of_surjective hsurj
  haveI := IsModuleTopology.topologicalAddGroup LL V
  have hU : IsOpen (Set.pi Set.univ fun _ : Fin n => Set.range (algebraMap O LL)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => hO
  refine M.toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    (Filter.mem_of_superset ((hopen _ hU).mem_nhds ⟨0, fun _ _ => ⟨0, by simp⟩, map_zero _⟩) ?_)
  rintro _ ⟨x, hx, rfl⟩
  rw [Fintype.linearCombination_apply]
  refine M.sum_mem fun i _ => ?_
  obtain ⟨a, ha⟩ := hx i (Set.mem_univ i)
  rw [← ha, algebraMap_smul]
  exact M.smul_mem a (hbM i)

theorem locLat_isOpen : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ T : LocLat G Qp LL O, IsOpen (T.L.T : Set T.V) := by
  intro G _ _ Qp _ _ LL _ _ _ O _ _ h T
  haveI := h.2.2.2.1
  exact isOpen_of_fg_of_span_eq_top h.2.2.2.2 T.L.T T.L.fg T.L.span

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUpUniMul
section
namespace GlobalTheory.UpperUnipotentMul

open Matrix

theorem isUpUni_mul {K : Type} [Field K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (hA : Formalism.MainNotions.S.IsUpUni A) (hB : Formalism.MainNotions.S.IsUpUni B) : Formalism.MainNotions.S.IsUpUni (A * B) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rcases lt_or_ge k i with hki | hik
    · rw [(hA i k).1 hki, zero_mul]
    · rw [(hB k j).1 (lt_of_lt_of_le hji hik), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hB i i).2 rfl, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [(hA i k).1 h, zero_mul]
      · rw [(hB k i).1 h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem main : ∀ {K : Type} [inst : Field K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K},
    Formalism.MainNotions.S.IsUpUni A → Formalism.MainNotions.S.IsUpUni B → Formalism.MainNotions.S.IsUpUni (A * B) :=
  fun hA hB => isUpUni_mul hA hB

end GlobalTheory.UpperUnipotentMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueAtEqUnitMul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ModelMetric
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ValueTwoGen

def genSec {Y : Scheme.{0}} {M : LB Y} (t : LB.Gen M) (ht : t.IsGen) : LB.Sec M where
  f := fun j => (t.s j).val
  compat := fun i j => congrArg Units.val (ht i j)

theorem exists_unit_gen {Y : Scheme.{0}} (M : LB Y) (hc : ⨆ j, M.U j = ⊤)
    (t t' : LB.Gen M) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ j, (t'.s j).val =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom (w : Γ(Y, ⊤)) * (t.s j).val := by
  obtain ⟨w, hw, -⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t' ht') t ht
  obtain ⟨w', hw', -⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t ht) t' ht'
  obtain ⟨_, -, hu⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t ht) t ht
  have h1 : (1 : Γ(Y, ⊤)) = w' * w := by
    have a := hu 1 (fun j => by simp [genSec])
    have b := hu (w' * w) (fun j => by
      have e1 := hw' j
      have e2 := hw j
      simp only [genSec] at e1 e2 ⊢
      rw [map_mul, _root_.mul_assoc, ← e2, ← e1])
    exact a.trans b.symm
  exact ⟨⟨w, w', by rw [_root_.mul_comm]; exact h1.symm, h1.symm⟩, fun j => hw j⟩

end GlobalTheory.ValueTwoGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelSenWeightMemWeightResidues
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem model_sen_mem : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.Ut i, ((u - Dt.w i : ℤ) : k) = x := by
  intro k G _ _ l n _ _ _ R F r Dt M A N hN i x hx
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  have hle := GlobalTheory.T.senMultiplicity_subquotient_lattice_le F B A₁ A j p Dt.w Dt.wst Nb (M.base_obj B Nb hB) hj hji hp hps
    (M.base_abc B Nb hB) i x
  obtain ⟨μ, -, hs⟩ := M.base_sen B Nb hB
  rw [hs i x] at hle
  have h0 : resCount (Dt.Ut i) (Dt.w i) x ≠ 0 := by
    intro h
    rw [h] at hle
    apply hx
    simpa using hle
  unfold resCount at h0
  obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero h0)
  classical
  rw [Multiset.mem_filter] at hu
  exact ⟨u, hu.1, hu.2⟩

end GlobalTheory.Models
end

