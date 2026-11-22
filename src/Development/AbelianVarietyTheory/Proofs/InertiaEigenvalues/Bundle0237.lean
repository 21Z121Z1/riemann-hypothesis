import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0227
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughOfPoly
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PassPoly

theorem aeval_mem_of_stable {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (D : Submodule L M) (hD : ∀ x ∈ D, f x ∈ D) (p : L[X]) : ∀ x ∈ D, Polynomial.aeval f p x ∈ D := by
  induction p using Polynomial.induction_on with
  | C a => intro x hx; simpa [Module.algebraMap_end_apply] using D.smul_mem a hx
  | add p q hp hq => intro x hx; simpa using D.add_mem (hp x hx) (hq x hx)
  | monomial n a ih =>
    intro x hx
    have := ih _ (hD x hx)
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    exact this

theorem mem_iSup_eigen {L M ι : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (D : Submodule L M) (hD : ∀ x ∈ D, f x ∈ D) (c : ι → L) (s : Finset ι) :
    (∀ a ∈ s, ∀ b ∈ s, c a = c b → a = b) → ∀ d ∈ D,
      Polynomial.aeval f (∏ a ∈ s, (X - C (c a))) d = 0 →
      d ∈ ⨆ a ∈ s, (D ⊓ LinearMap.ker (f - c a • LinearMap.id)) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _ d _ h; simp at h; simp [h]
  | insert a t hat ih =>
    intro hinj d hd h
    rw [Finset.prod_insert hat] at h
    have hcop : IsCoprime (X - C (c a)) (∏ b ∈ t, (X - C (c b))) := by
      refine IsCoprime.prod_right fun b hb => ?_
      refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub (IsUnit.mk0 _ (sub_ne_zero.2 fun e => hat ?_))
      rw [hinj a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb) e]
      exact hb
    obtain ⟨u, v, huv⟩ := hcop
    set Q := ∏ b ∈ t, (X - C (c b)) with hQ
    have hdec : d = Polynomial.aeval f (u * (X - C (c a))) d + Polynomial.aeval f (v * Q) d := by
      rw [← LinearMap.add_apply, ← map_add, huv, map_one, Module.End.one_apply]
    rw [Finset.iSup_insert, hdec, add_comm]
    refine Submodule.add_mem_sup ?_ ?_
    · refine ⟨aeval_mem_of_stable f D hD _ d hd, ?_⟩
      have h1 : Polynomial.aeval f (X - C (c a)) (Polynomial.aeval f (v * Q) d) = 0 := by
        rw [← Module.End.mul_apply, ← map_mul,
          show (X - C (c a)) * (v * Q) = v * ((X - C (c a)) * Q) by ring, map_mul,
          Module.End.mul_apply, h, map_zero]
      simpa [Module.algebraMap_end_apply] using h1
    · refine ih (fun x hx y hy => hinj x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)) _
        (aeval_mem_of_stable f D hD _ d hd) ?_
      rw [← Module.End.mul_apply, ← map_mul,
          show Q * (u * (X - C (c a))) = u * ((X - C (c a)) * Q) by ring, map_mul,
          Module.End.mul_apply, h, map_zero]

section
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
    (ρ : Representation LL G V)

theorem actVB_mul' (g h : G) (x : V ⊗[Qp] B) :
    actVB PC.PD ρ (g * h) x = actVB PC.PD ρ g (actVB PC.PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem actVB_one' (x : V ⊗[Qp] B) : actVB PC.PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem actVB_resH (h : PC.H) (x : V ⊗[Qp] B) :
    actVB PC.PD' (PC.resH ρ) h x = actVB PC.PD ρ (h : G) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, PotCrysData.resH, PC.actB_eq]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_Dpcris_iff (x : V ⊗[Qp] B) :
    x ∈ PC.Dpcris ρ ↔ ∀ g ∈ PC.H, actVB PC.PD ρ g x = x := by
  simp only [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, actVB_resH, Subtype.forall]

theorem Dpcris_stable (g : G) : ∀ x ∈ PC.Dpcris ρ, actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  intro x hx
  rw [mem_Dpcris_iff] at hx ⊢
  intro h hh
  have h1 : g⁻¹ * h * g ∈ PC.H := by simpa using PC.normal.conj_mem h hh g⁻¹
  rw [← actVB_mul', show h * g = g * (g⁻¹ * h * g) by group, actVB_mul', hx _ h1]

theorem inertiaThrough_of_poly (Sig : Finset (PC.Iner →* LLˣ))
    (h1 : ∀ a ∈ Sig, ∀ g : PC.Iner, (g : G) ∈ PC.H → a g = 1)
    (h2 : ∀ a ∈ Sig, Nat.Coprime (orderOf a) PC.PD.p)
    (h3 : ∀ (g : PC.Iner), ∀ d ∈ PC.Dpcris ρ, (Polynomial.aeval (actVB PC.PD ρ (g : G))
      (∏ a ∈ Sig, (X - C ((a g : LLˣ) : LL)))) d = 0)
    (h4 : ∃ γ : PC.Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧
      ∀ g : PC.Iner, ∃ (n : ℕ) (u : PC.Iner), ((u : G) ∈ PC.H) ∧ g = γ ^ n * u) :
    PC.InertiaThrough ρ Sig := by
  refine ⟨h1, h2, le_antisymm ?_ ?_⟩
  · obtain ⟨γ, hsep, hgen⟩ := h4
    intro d hd
    have := mem_iSup_eigen (actVB PC.PD ρ (γ : G)) (PC.Dpcris ρ) (Dpcris_stable PC ρ γ)
      (fun a : PC.Iner →* LLˣ => ((a γ : LLˣ) : LL)) Sig
      (fun a ha b hb e => hsep a ha b hb (Units.ext e)) d hd (h3 γ d hd)
    refine (iSup₂_mono (fun a ha => ?_) : _ ≤ ⨆ a ∈ Sig, PC.Eig ρ PC.Iner a) this
    rintro x ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have hγ : actVB PC.PD ρ (γ : G) x = ((a γ : LLˣ) : LL) • x := by
      simpa [sub_eq_zero] using hx'
    have hn : ∀ n : ℕ, actVB PC.PD ρ ((γ : G) ^ n) x = ((a γ : LLˣ) : LL) ^ n • x := by
      intro n
      induction n with
      | zero => simp [actVB_one']
      | succ n ih => rw [pow_succ, actVB_mul', hγ, map_smul, ih, smul_smul, pow_succ, mul_comm]
    simp only [Submodule.coe_iInf, Set.mem_iInter, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro g
    obtain ⟨n, u, hu, rfl⟩ := hgen g
    rw [map_mul, h1 a ha u hu, mul_one, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, actVB_mul',
      (mem_Dpcris_iff PC ρ x).1 hx u hu, hn, Units.val_pow_eq_pow_val]
  · exact iSup₂_le fun a _ => inf_le_left

end

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)), (∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1) → (∀ a ∈ Sig, Nat.Coprime (orderOf a) l) → (∀ (g : (pc P h hN hF hS).Iner), ∀ d ∈ (pc P h hN hF hS).Dpcris ρ, (Polynomial.aeval (actVB (P.PD K) ρ (g : ↥(GK K))) (∏ a ∈ Sig, (X - C ((a g : (↥LL.1)ˣ) : ↥LL.1)))) d = 0) → (∃ γ : (pc P h hN hF hS).Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧ ∀ g : (pc P h hN hF hS).Iner, ∃ (n : ℕ) (u : (pc P h hN hF hS).Iner), ((u : ↥(GK K)) ∈ (pc P h hN hF hS).H) ∧ g = γ ^ n * u) → (pc P h hN hF hS).InertiaThrough ρ Sig := by
  intro l _ P K K' LL h hN hF hS V _ _ _ _ ρ Sig h1 h2 h3 h4
  refine inertiaThrough_of_poly (pc P h hN hF hS) ρ Sig h1 ?_ h3 h4
  have hp : (pc P h hN hF hS).PD.p = l := P.PD_p K
  rw [hp]
  exact h2

end GlobalTheory.PassPoly

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDRAndDdRLeFilZeroOfTwist
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

section TwistDeRham

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem deRhamTwist_galoisAct_period (g : G) :
    PD.actdR g (PD.ι PD.t) = ((PD.χ g : Qpˣ) : Qp) • PD.ι PD.t := by
  rw [← PD.ι_comm, PD.t_act, ← algebraMap_smul K₀ ((PD.χ g : Qpˣ) : Qp) PD.t, map_smul,
    algebraMap_smul]

theorem drTwist_pow_mem (e : ℕ) : (PD.ι PD.t) ^ e ∈ PD.Fil (e : ℤ) := by
  induction e with
  | zero => simpa using PD.one_mem
  | succ n ih =>
    rw [pow_succ]
    exact_mod_cast PD.Fil_mul _ _ _ _ ih PD.mem_filtration_one

theorem drTwist_Fil_le (e : ℕ) : PD.Fil (e : ℤ) ≤ PD.Fil 0 := by
  induction e with
  | zero => simp
  | succ n ih =>
    refine le_trans ?_ ih
    exact_mod_cast PD.Fil_anti (n : ℤ)

noncomputable def drTwistMap (e : ℕ) : K →ₗ[Qp] BdR :=
  (LinearMap.mulRight Qp ((PD.ι PD.t) ^ e)) ∘ₗ (IsScalarTower.toAlgHom Qp K BdR).toLinearMap

theorem drTwistMap_apply (e : ℕ) (k : K) :
    drTwistMap PD e k = algebraMap K BdR k * (PD.ι PD.t) ^ e := rfl

theorem drTwistMap_injective (e : ℕ) : Function.Injective (drTwistMap PD e) := by
  have hnt : Nontrivial BdR := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact PD.not_mem_filtration_two (by rw [Subsingleton.elim (PD.ι PD.t) 0]; exact Submodule.zero_mem _)
  intro a b hab
  rw [drTwistMap_apply, drTwistMap_apply] at hab
  have hu : IsUnit ((PD.ι PD.t) ^ e) := (PD.t_unit.map PD.ι).pow e
  exact (algebraMap K BdR).injective (hu.mul_right_cancel hab)

theorem drTwistMap_mem (e : ℕ) (k : K) : drTwistMap PD e k ∈ PD.Fil 0 := by
  rw [drTwistMap_apply, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (drTwist_Fil_le PD e (drTwist_pow_mem PD e))

theorem drTwist_act_pow (e : ℕ) (g : G) :
    PD.actdR g ((PD.ι PD.t) ^ e) = ((PD.χ g : Qpˣ) : Qp) ^ e • (PD.ι PD.t) ^ e := by
  rw [map_pow, deRhamTwist_galoisAct_period, smul_pow]

theorem drTwistMap_fixed (e : ℕ) (g : G) (k : K) :
    (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g (drTwistMap PD e k) = drTwistMap PD e k := by
  rw [drTwistMap_apply, map_mul, AlgEquiv.commutes, drTwist_act_pow, mul_smul_comm, smul_smul,
    ← mul_pow, inv_mul_cancel₀ (PD.χ g).ne_zero, one_pow, one_smul]

theorem drTwistMap_range (e : ℕ) (y : BdR)
    (hy : ∀ g, (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g y = y) :
    ∃ k, drTwistMap PD e k = y := by
  have hu : IsUnit ((PD.ι PD.t) ^ e) := (PD.t_unit.map PD.ι).pow e
  obtain ⟨z, hz⟩ := hu.exists_left_inv
  have hyz : y = (y * z) * (PD.ι PD.t) ^ e := by rw [mul_assoc, hz, mul_one]
  obtain ⟨k, hk⟩ := PD.invdR (y * z) (fun g => by
    apply hu.mul_right_cancel
    have h := hy g
    rw [hyz, map_mul, drTwist_act_pow, mul_smul_comm, smul_smul,
      ← mul_pow, inv_mul_cancel₀ (PD.χ g).ne_zero, one_pow, one_smul] at h
    exact h)
  exact ⟨k, by rw [drTwistMap_apply, hk, ← hyz]⟩

variable {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V)

theorem drTwist_act_tmul (e : ℕ)
    (h : ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) (g : G) (v : V) (y : BdR) :
    actVdR PD ρ g (v ⊗ₜ[Qp] y) =
      v ⊗ₜ[Qp] ((((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g y) := by
  have : actVdR PD ρ g (v ⊗ₜ[Qp] y) = ρ g v ⊗ₜ[Qp] PD.actdR g y := rfl
  rw [this, h, ← map_inv₀, ← map_pow, algebraMap_smul, smul_tmul]

theorem drTwist_range (e : ℕ)
    (h : ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) :
    LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (drTwistMap PD e)) =
      DdR PD ρ := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | tmul v k =>
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, AlgebraTensorModule.map_tmul, sub_eq_zero]
      intro g
      rw [drTwist_act_tmul PD ρ e h, drTwistMap_fixed]
  · intro x hx
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hx
    let b := Module.Basis.ofVectorSpace Qp V
    let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) b
    have hE : ∀ g (x : V ⊗[Qp] BdR) i, E (actVdR PD ρ g x) i =
        (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g (E x i) := by
      intro g x i
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb, smul_add]
      | tmul v y =>
        rw [drTwist_act_tmul PD ρ e h]
        simp only [E, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
        rw [← algebraMap_smul K (b.repr v i) y, map_smul, algebraMap_smul, smul_comm]
    have hx' : x = E.symm (E x) := (E.symm_apply_apply x).symm
    rw [hx', TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    obtain ⟨k, hk⟩ := drTwistMap_range PD e (E x i) (fun g => by rw [← hE, hx g])
    exact ⟨b i ⊗ₜ k, by rw [AlgebraTensorModule.map_tmul, hk]; rfl⟩

end TwistDeRham

theorem isDR_and_DdR_le_Fil_zero_of_twist : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) (e : ℕ), (∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) → IsDR PD ρ ∧ DdR PD ρ ≤ FilV PD (LL := LL) (V := V) 0 := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ _ ρ e h
  have hr := drTwist_range PD ρ e h
  constructor
  · have hinj : Function.Injective
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (drTwistMap PD e)) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ (drTwistMap_injective PD e)
    have := PD.finK
    unfold IsDR
    rw [← hr, LinearMap.finrank_range_of_inj hinj, Module.finrank_tensorProduct, mul_comm]
  · rw [← hr]
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | tmul v k => exact ⟨v ⊗ₜ ⟨drTwistMap PD e k, drTwistMap_mem PD e k⟩, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfRestrictGaloisDescent
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamDescent

theorem finrank_fixed {R G M K L : Type} [Field R] [Group G] [AddCommGroup M] [Module R M]
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : G →* Module.End R M) (m : L →+* Module.End R M) (ε : G →* (L ≃ₐ[K] L))
    (hs : Function.Surjective ε) (hε : ∀ g a x, A g (m a x) = m (ε g a) (A g x))
    (D D' : Submodule R M) (hD : ∀ x, x ∈ D ↔ ∀ g, A g x = x)
    (hD' : ∀ x, x ∈ D' ↔ ∀ g, ε g = 1 → A g x = x) :
    Module.finrank R D' = Module.finrank K L * Module.finrank R D := by
  classical
  have hc : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rw [← Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank K L
  let b : Module.Basis (L ≃ₐ[K] L) K L :=
    (Module.finBasis K L).reindex (Fintype.equivFinOfCardEq hc).symm
  let μ : Module.Basis (L ≃ₐ[K] L) K L := b.traceDual
  let Pm : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := Matrix.of fun σ i => σ (b i)
  let Qm : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := Matrix.of fun j σ => σ (μ j)
  have hQP : Qm * Pm = 1 := by
    ext j i
    simp only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, ← map_mul]
    rw [← trace_eq_sum_automorphisms, Module.Basis.trace_traceDual_mul, Matrix.one_apply]
    by_cases h : j = i
    · simp [h]
    · simp [h, Ne.symm h]
  have hPQ : Pm * Qm = 1 := mul_eq_one_comm.1 hQP
  have h1 : ∀ j i, ∑ σ : L ≃ₐ[K] L, σ (μ j) * σ (b i) = if j = i then 1 else 0 := fun j i => by
    have := congrFun (congrFun hQP j) i
    simpa only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, Matrix.one_apply] using this
  have h2 : ∀ σ : L ≃ₐ[K] L, ∑ i, b i * σ (μ i) = if 1 = σ then 1 else 0 := fun σ => by
    have := congrFun (congrFun hPQ 1) σ
    simpa only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, Matrix.one_apply,
      AlgEquiv.one_apply] using this
  choose s hs' using hs
  have hm : ∀ a, ∀ x ∈ D', m a x ∈ D' := fun a x hx => by
    rw [hD'] at hx ⊢
    intro g hg
    rw [hε, hg, hx g hg, AlgEquiv.one_apply]
  have hDD : D ≤ D' := fun x hx => (hD' x).2 fun g _ => (hD x).1 hx g
  have hA : ∀ x ∈ D', ∀ g g', ε g = ε g' → A g x = A g' x := fun x hx g g' h => by
    have := (hD' x).1 hx (g'⁻¹ * g) (by rw [map_mul, map_inv, h, inv_mul_cancel])
    conv_rhs => rw [← this]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  let Φ₀ : ((L ≃ₐ[K] L) → D) →ₗ[R] M :=
    ∑ i, (m (b i)) ∘ₗ D.subtype ∘ₗ LinearMap.proj i
  have hΦ : ∀ x, Φ₀ x = ∑ i, m (b i) (x i) := fun x => by
    simp [Φ₀]
  have hinj : Function.Injective Φ₀ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h3 : ∀ σ : L ≃ₐ[K] L, ∑ i, m (σ (b i)) (x i) = 0 := fun σ => by
      have := congrArg (A (s σ)) hx
      rw [hΦ, map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hε, hs', (hD _).1 (x i).2]
    funext j
    apply Subtype.ext
    have h4 : ∑ σ : L ≃ₐ[K] L, m (σ (μ j)) (∑ i, m (σ (b i)) (x i)) = 0 := by
      simp only [h3, map_zero, Finset.sum_const_zero]
    simp only [map_sum, ← Module.End.mul_apply, ← map_mul m] at h4
    rw [Finset.sum_comm] at h4
    simp only [← LinearMap.sum_apply, ← map_sum m, h1] at h4
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Ne.symm hi]) (by simp)] at h4
    simpa using h4
  have hr : LinearMap.range Φ₀ = D' := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hΦ]
      exact D'.sum_mem fun i _ => hm _ _ (hDD (x i).2)
    · intro x hx
      refine ⟨fun i => ⟨∑ σ, A (s σ) (m (μ i) x), (hD _).2 fun g => ?_⟩, ?_⟩
      · rw [map_sum, ← Equiv.sum_comp (Equiv.mulLeft (ε g))
          (fun σ => A (s σ) (m (μ i) x))]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Module.End.mul_apply, ← map_mul]
        exact hA _ (hm _ _ hx) _ _ (by simp [hs'])
      · rw [hΦ]
        have hmm : ∀ a a' y, m a (m a' y) = m (a * a') y := fun a a' y => by
          rw [map_mul, Module.End.mul_apply]
        simp only [hε, hs', map_sum, hmm]
        rw [Finset.sum_comm]
        simp only [← LinearMap.sum_apply, ← map_sum m, h2]
        rw [Finset.sum_eq_single 1 (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
        simpa using (hD' x).1 hx _ (hs' 1)
  rw [← hr, LinearMap.finrank_range_of_inj hinj]
  by_cases hf : Module.Finite R D
  · rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, hc, smul_eq_mul]
  · rw [Module.finrank_of_not_finite hf, mul_zero, Module.finrank_of_not_finite]
    intro h
    exact hf (Module.Finite.of_surjective
      (LinearMap.proj (R := R) (φ := fun _ : L ≃ₐ[K] L => D) (1 : L ≃ₐ[K] L))
      (fun y => ⟨fun _ => y, rfl⟩))

open GlobalTheory.JumpDescent TensorProduct in

theorem isDR_of_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l)
    (hle : GK K' ≤ GK K), K.1 ≤ K'.1 → (∀ g ∈ GK K, ∀ x ∈ K'.1, g x ∈ K'.1) →
    ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      IsDR (P.PD K') (V := V) (ρ.comp (Subgroup.inclusion hle)) → IsDR (P.PD K) ρ := by
  intro l _ P K K' LL hle h hst V _ _ _ _ ρ hρ
  unfold IsDR at hρ ⊢
  haveI : FiniteDimensional ℚ_[l] ↥K'.1 := K'.2
  let L : IntermediateField ↥K.1 (Om l) := IntermediateField.extendScalars h
  haveI : FiniteDimensional ℚ_[l] ↥L := K'.2
  haveI : FiniteDimensional ↥K.1 ↥L := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  haveI : Normal ↥K.1 (Om l) := Normal.tower_top_of_normal ℚ_[l] _ _
  let e : ↥(GK K) ≃* (Om l ≃ₐ[↥K.1] Om l) := IntermediateField.fixingSubgroupEquiv K.1
  have he : ∀ (g : ↥(GK K)) (x : Om l), e g x = (g : GQ l) x := fun _ _ => rfl
  haveI : Normal ↥K.1 ↥L := IntermediateField.normal_iff_forall_map_le'.2 fun σ => by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, rfl⟩ := e.surjective σ
    exact hst g.1 g.2 x hx
  haveI : IsGalois ↥K.1 ↥L := {}
  let ε : ↥(GK K) →* (↥L ≃ₐ[↥K.1] ↥L) := (AlgEquiv.restrictNormalHom ↥L).comp e.toMonoidHom
  have hεa : ∀ (g : ↥(GK K)) (x : ↥L), ((ε g x : ↥L) : Om l) = (g : GQ l) x := fun g x =>
    AlgEquiv.restrictNormalHom_apply L (e g) x
  let A : ↥(GK K) →* Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := actVdR (P.PD K) ρ
      map_one' := by ext v b; simp [actVdR_tmul]
      map_mul' := fun g g' => by ext v b; simp [actVdR_tmul] }
  let m : ↥L →+* Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := fun c => mulOm P (c : Om l)
      map_one' := by ext v b; simp [mulOm_tmul]
      map_mul' := fun g g' => by ext v b; simp [mulOm_tmul, mul_assoc]
      map_zero' := by ext v b; simp [mulOm_tmul]
      map_add' := fun g g' => by ext v b; simp [mulOm_tmul, add_mul, tmul_add] }
  have key := finrank_fixed A m ε
    ((AlgEquiv.restrictNormalHom_surjective (F := ↥K.1) (K₁ := ↥L) (Om l)).comp e.surjective)
    (fun g c x => by
      change actVdR (P.PD K) ρ g (mulOm (LL := ↥LL.1) P (c : Om l) x) =
        mulOm (LL := ↥LL.1) P ((ε g c : ↥L) : Om l) (actVdR (P.PD K) ρ g x)
      rw [hεa]
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul v b => simp [mulOm_tmul, actVdR_tmul, P.actQdR_Om]
      | add y z hy hz => simp only [map_add, hy, hz])
    (DdR (P.PD K) ρ) (DdR (P.PD K') (ρ.comp (Subgroup.inclusion hle)))
    (fun x => mem_DdR P K ρ x)
    (fun x => by
      rw [mem_DdR]
      constructor
      · intro hx g hg
        have hg' : g.1 ∈ GK K' := fun a => by
          have := hεa g ⟨a.1, a.2⟩
          rw [hg] at this
          exact this.symm
        have := hx ⟨g.1, hg'⟩
        rw [actVdR_comp P h] at this
        exact this
      · intro hx g
        rw [actVdR_comp P h]
        apply hx
        ext a
        rw [hεa]
        exact g.2 ⟨a.1, a.2⟩)
  have hfin : Module.finrank ℚ_[l] ↥K'.1 = Module.finrank ℚ_[l] ↥K.1 * Module.finrank ↥K.1 ↥L :=
    (Module.finrank_mul_finrank ℚ_[l] ↥K.1 ↥L).symm
  have hpos : 0 < Module.finrank ↥K.1 ↥L := Module.finrank_pos
  rw [key, hfin] at hρ
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hρ]
  ring

end GlobalTheory.DeRhamDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodCyclotomicCharReducesModPrimePowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodCyclotomicChar_reduces_mod_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (r : ℕ) (g : ↥(GK K)), ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧ (PadicInt.toZModPow r u : ZMod (l ^ r)) = ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) := by
  first | exact @GlobalTheory.CycLevel.chi_reduces | exact GlobalTheory.CycLevel.chi_reduces | (intros; apply GlobalTheory.CycLevel.chi_reduces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanCyclotomicTwoCocyclesFiniteExtensionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_cyclotomic_twoCocycles_finite_extension : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0)) → ∃ z0 : ↥(GK K) × ↥(GK K) → LL, (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → LL, Continuous z → (∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : LL, CobL (P.PD K) (z - x • z0) := by
  first | exact @GlobalTheory.span_cocycles_cyc_ext | exact GlobalTheory.span_cocycles_cyc_ext | (intros; apply GlobalTheory.span_cocycles_cyc_ext <;> assumption)
end

