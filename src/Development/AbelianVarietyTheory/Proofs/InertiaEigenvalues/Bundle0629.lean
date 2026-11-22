import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0620
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0361
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0622
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlochKatoCocycleOfCrysDeRhamPair
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.FundDel

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

lemma actVB_tmul' (g : G) (v : V) (b : B) :
    actVB PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actB g b := rfl

lemma actVdR_tmul' (g : G) (v : V) (b : BdR) :
    actVdR PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actdR g b := rfl

lemma φVB_tmul' (v : V) (b : B) :
    φVB PD (LL := LL) (V := V) (v ⊗ₜ[Qp] b) = v ⊗ₜ[Qp] PD.φ b := rfl

lemma ιV_tmul' (v : V) (b : B) :
    ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] b) = v ⊗ₜ[Qp] PD.ι b := rfl

lemma φVB_actVB' (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => rw [actVB_tmul', φVB_tmul', φVB_tmul', actVB_tmul', PD.φ_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma ιV_actVB' (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => rw [actVB_tmul', ιV_tmul', ιV_tmul', actVdR_tmul', PD.ι_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma actVB_mul' (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b =>
    rw [actVB_tmul', actVB_tmul', actVB_tmul', map_mul, map_mul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

lemma actVdR_mem_FilV' (g : G) (a : ℤ) (y : V ⊗[Qp] BdR)
    (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    actVdR PD ρ g y ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Submodule.zero_mem]
  | tmul v b =>
    exact ⟨ρ g v ⊗ₜ[Qp] ⟨PD.actdR g b.1, PD.Fil_G g a _ b.2⟩, rfl⟩
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy

include PD in
lemma nontrivial_B' : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim PD.t 0, map_zero]
  exact Submodule.zero_mem _

include PD in
lemma tmul_one_injective' {v w : V} (h : v ⊗ₜ[Qp] (1 : B) = w ⊗ₜ[Qp] (1 : B)) : v = w := by
  haveI := nontrivial_B' PD
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one Qp (one_ne_zero : (1 : B) ≠ 0)
  have := congrArg (fun z => TensorProduct.rid Qp V (LinearMap.lTensor V f z)) h
  simpa [hf] using this

lemma sub_fixed_mem (d₁ : V ⊗[Qp] B) (h₁ : d₁ ∈ Dcris PD ρ) (d₂ : V ⊗[Qp] BdR) (h₂ : d₂ ∈ DdR PD ρ)
    (x : V ⊗[Qp] B) (y : V ⊗[Qp] BdR) (hy : y ∈ FilV PD (LL := LL) (V := V) 0)
    (hx : x - φVB PD (LL := LL) (V := V) x = d₁) (hxy : ιV PD (LL := LL) (V := V) x - y = d₂)
    (g : G) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x - x) = actVB PD ρ g x - x ∧
      ιV PD (LL := LL) (V := V) (actVB PD ρ g x - x) ∈ FilV PD (LL := LL) (V := V) 0 := by
  have e₁ : actVB PD ρ g d₁ - d₁ = 0 := (Submodule.mem_iInf _).1 h₁ g
  have e₂ : actVdR PD ρ g d₂ - d₂ = 0 := (Submodule.mem_iInf _).1 h₂ g
  rw [← hx, map_sub] at e₁
  rw [← hxy, map_sub] at e₂
  constructor
  · rw [map_sub, φVB_actVB', ← sub_eq_zero, ← neg_eq_zero, ← e₁]
    abel
  · have : ιV PD (LL := LL) (V := V) (actVB PD ρ g x - x) = actVdR PD ρ g y - y := by
      rw [map_sub, ιV_actVB', ← sub_eq_zero, ← e₂]
      abel
    rw [this]
    exact Submodule.sub_mem _ (actVdR_mem_FilV' PD ρ g 0 y hy) hy

lemma cocycle_of_tmul_one (x : V ⊗[Qp] B) (c : G → V)
    (hc : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) (g h : G) :
    c (g * h) = c g + ρ g (c h) := by
  apply tmul_one_injective' PD
  have e : ρ g (c h) ⊗ₜ[Qp] (1 : B) = actVB PD ρ g (c h ⊗ₜ[Qp] (1 : B)) := by
    rw [actVB_tmul', map_one]
  rw [add_tmul, e, hc, hc, hc, map_sub, actVB_mul']
  abel

end General

theorem connecting_cocycle : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, ∀ d₁ ∈ Dcris (P.PD K) A.ρ, ∀ d₂ ∈ DdR (P.PD K) A.ρ, ∃ (x : A.V ⊗[ℚ_[l]] P.R.B) (y : A.V ⊗[ℚ_[l]] P.R.BdR) (c : ↥(GK K) → A.V), y ∈ FilV (P.PD K) (LL := LL) (V := A.V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := A.V) x = d₁ ∧ ιV (P.PD K) (LL := LL) (V := A.V) x - y = d₂ ∧ c ∈ finiteCocycles (P.PD K) A.ρ ∧ ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x := by
  intro l _ P AI T K LL _ _ _ O _ _ hO A d₁ h₁ d₂ h₂
  obtain ⟨hsurj, hker⟩ := GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI T K LL A.V
  obtain ⟨x, y, hy, hx, hxy⟩ := hsurj d₁ d₂
  have key : ∀ g, ∃ v : A.V, actVB (P.PD K) A.ρ g x - x = v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := fun g =>
    hker _ (sub_fixed_mem (P.PD K) A.ρ d₁ h₁ d₂ h₂ x y hy hx hxy g).1
      (sub_fixed_mem (P.PD K) A.ρ d₁ h₁ d₂ h₂ x y hy hx hxy g).2
  choose c hc using key
  have hc' : ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x := fun g => (hc g).symm
  have hcont : Continuous c :=
    GlobalTheory.FundCont.contCore_tied l P AI T K LL O hO A 0 Fin.elim0 Fin.elim0 (fun i => i.elim0) x c
      (fun g => by rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add]; exact hc' g)
  exact ⟨x, y, c, hy, hx, hxy,
    ⟨⟨hcont, cocycle_of_tmul_one (P.PD K) A.ρ x c hc'⟩, x, hc'⟩, hc'⟩

end GlobalTheory.FundDel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedPeriodsDiscAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

theorem frobenius_ev_X_eq {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    WittVector.frobenius (bk.ev X) = bk.ev X ^ l := by
  rw [← bk.ev_frob, frobS_X, map_pow]

theorem BK.ρ₀_pos' {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ :=
  NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)

theorem BK.ρ₀_lt_one' {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : bk.ρ₀ < 1 :=
  NNReal.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hl.out.one_lt)
    (neg_neg_of_pos (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))

theorem tendsto_cofinite_prod_of_finite {ι α E : Type} [Finite α] [TopologicalSpace E] {x : E}
    (f : ι × α → E) (h : ∀ a, Filter.Tendsto (fun i => f (i, a)) Filter.cofinite (nhds x)) :
    Filter.Tendsto f Filter.cofinite (nhds x) := by
  intro U hU
  have hs : ∀ a, ((fun i => f (i, a)) ⁻¹' U)ᶜ.Finite := fun a => h a hU
  rw [Filter.mem_map, Filter.mem_cofinite]
  refine (Set.finite_iUnion fun a => (hs a).image (fun i => (i, a))).subset ?_
  rintro ⟨i, a⟩ hia
  exact Set.mem_iUnion.2 ⟨a, i, hia, rfl⟩

theorem exists_bounded_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∃ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (k : ℕ) (v : ι → Matrix (Fin d) (Fin d) (Ainf l)) (Z : ι → Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (∀ (n : ℕ) (a b : Fin d), {i | v i a b ∉ (bk.J ^ n).map bk.ev}.Finite) ∧ (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → ∀ i, s.W * (Z i).map j = (v i).map bk.iA) ∧ ∀ a b : Fin d, HasSum (fun i => bk.iA (v i a b * TB.b i)) (bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0)) := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hρ0 := bk.ρ₀_pos'
  have hρ1 := bk.ρ₀_lt_one'
  have hj0 : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j0 : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ :=
    Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) bk.ev hj0
  have hj0d : IsDiscMap bk.ev j0 := isDiscMap_map _ _
  have hΦ0 : ‖toDisc l (bk.ev X) bk.ρ₀ (WittVector.frobenius (bk.ev X))‖ ≤ bk.ρ₀ := by
    rw [frobenius_ev_X_eq]
    refine (norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) l hρ0).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1.le) (Fact.out : l.Prime).ne_zero
  let Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ :=
    Disc.map (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) WittVector.frobenius hΦ0
  have hΦ : IsDiscMap WittVector.frobenius Φ := isDiscMap_map _ _
  obtain ⟨cD, hc1, hc2, hc3, hc4, hc5, -, -, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j0 hj0d
  have hrec := GlobalTheory.T.seed_coeff_recurrence_alt l K bk τ hτ d ρ hρ s ι TB j0 hj0d cD hc1 hc2 hc5 hc3 Φ hΦ
  let V : ι → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀) := fun i => s.W * (s.W'.map (cD i)).map j0
  let Vκ : ι × (Fin d × Fin d) → bk.DA bk.ρ₀ := fun p => V p.1 p.2.1 p.2.2
  let c : ι × (Fin d × Fin d) → ι × (Fin d × Fin d) → Ainf l := fun p q =>
    if p.2 = q.2 then bk.ev (TB.c q.1 (WittVector.frobenius (TB.b p.1))) else 0
  have hcfin : ∀ p (n : ℕ), {q | c p q ∉ (bk.J ^ n).map bk.ev}.Finite := by
    rintro ⟨i, ab⟩ n
    refine ((TB.fin (WittVector.frobenius (TB.b i)) n).image fun i₁ => (i₁, ab)).subset ?_
    rintro ⟨i₁, ab'⟩ hq
    by_cases e : ab = ab'
    · subst e
      refine ⟨i₁, fun hm => hq ?_, rfl⟩
      simp only [c, if_pos rfl]
      exact Ideal.mem_map_of_mem _ hm
    · exact (hq (by simp [c, e])).elim
  have hj0c : Continuous j0 :=
    AddMonoidHomClass.continuous_of_bound j0 1 fun y => (hj0d.norm_le y).trans (one_mul _).ge
  have hV : Filter.Tendsto Vκ Filter.cofinite (nhds 0) := by
    refine tendsto_cofinite_prod_of_finite Vκ fun ab => ?_
    have := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun m _ =>
      (tendsto_const_nhds (x := s.W ab.1 m)).mul ((hj0c.tendsto 0).comp (hc4 (s.W' m ab.2)))
    simpa [Vκ, V, Matrix.mul_apply] using this
  have hrecκ : ∀ q, HasSum (fun p => Φ (Vκ p) * toDisc l (bk.ev X) bk.ρ₀ (c p q))
      (toDisc l (bk.ev X) bk.ρ₀ (bk.ev bk.E) ^ (2 * s.N) * Vκ q) := by
    rintro ⟨i₁, a, b⟩
    have hg : Function.Injective (fun i : ι => (i, (a, b))) := fun x y h => (Prod.mk.inj h).1
    refine (hg.hasSum_iff ?_).1 ?_
    · rintro ⟨i, a', b'⟩ hx
      have hne : (a', b') ≠ (a, b) := fun e => hx ⟨i, by simp [e]⟩
      simp [c, hne]
    · convert hrec i₁ a b using 1
      · funext i
        simp [c, Vκ, V]
      · rfl
  obtain ⟨k, v, hv1, hv2⟩ := GlobalTheory.T.exists_bounded_of_phi_equation_disc l K bk (Ainf l) bk.ev ι TB WittVector.frobenius (frobenius_ev_X_eq bk)
    Φ hΦ _ c hcfin (2 * s.N) Vκ hV hrecκ
  refine ⟨ι, TB, k, fun i => Matrix.of fun a b => v (i, (a, b)),
    fun i => (l : bk.DS bk.ρ₀) ^ k • s.W'.map (cD i), ?_, ?_, ?_⟩
  · intro n a b
    have hg : Function.Injective (fun i : ι => (i, (a, b))) := fun x y h => (Prod.mk.inj h).1
    exact (hv2 n).preimage hg.injOn
  · intro j hj i
    have e := IsDiscMap.unique hj hj0d
    subst e
    ext a b
    show (s.W * ((l : bk.DS bk.ρ₀) ^ k • s.W'.map (cD i)).map j0) a b = bk.iA (v (i, (a, b)))
    rw [hv1]
    simp only [Vκ, V, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow,
      map_natCast, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  · intro a b
    have hs := (hasSum_sum (s := (Finset.univ : Finset (Fin d))) fun m _ =>
      (hc5 (s.W' m b)).mul_left (s.W a m)).mul_left ((l : bk.DA bk.ρ₀) ^ k)
    have hW := congrFun (congrFun s.W_mul a) b
    rw [Matrix.mul_apply] at hW
    rw [hW] at hs
    have hf : (fun i => bk.iA ((Matrix.of fun a b => v (i, (a, b))) a b * TB.b i)) =
        fun i => (l : bk.DA bk.ρ₀) ^ k * ∑ m, s.W a m * (j0 (cD i (s.W' m b)) * toDisc l (bk.ev X) bk.ρ₀ (TB.b i)) := by
      funext i
      rw [map_mul, Matrix.of_apply, hv1]
      simp only [Vκ, V, Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hval : bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0) =
        (l : bk.DA bk.ρ₀) ^ k * (bk.iA τ ^ (2 * s.N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))) a b := by
      rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [hf, hval]
    exact hs

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCutoffFunctionTorusGLStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cutoff_function_torus_GL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ f' : Gl r F → ℂ, IsTest f' → ∃ α : GL (Fin r) F → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ g : GL (Fin r) F, (∃ v w : Fin r → F, f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0) → ∀ s₀ : A.Kˣ, ∫ s, α (g * LinDesc.tm A hG s₀ * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1 := by
  first | exact @GlobalTheory.JR.LinDesc.exists_cutoff_torus | exact GlobalTheory.JR.LinDesc.exists_cutoff_torus | (intros; apply GlobalTheory.JR.LinDesc.exists_cutoff_torus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqTmulOneOfMonodromyFrobeniusFiltration
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_eq_tmul_one_of_mon_phi_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 → phiV P ℚ_[l] V z = z → LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 → ∃ v : V, z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
  intro l _ P AI T ι hι K V _ _ z hN hφ hF
  obtain ⟨w, rfl⟩ := (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V z).mp hN
  rw [GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K V w] at hφ
  have hw := crisIncl_injective P hφ
  have key : ∀ x : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V x) =
      ιV (P.PD K) (LL := ℚ_[l]) (V := V) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ιV, hι, P.PD_ι]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [key] at hF
  obtain ⟨v, rfl⟩ := (GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI T K ℚ_[l] V).2 w hw hF
  exact ⟨v, by rw [crisIncl_tmul, Polynomial.C_1]⟩

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivStableLatticeIntegralCharacterStatement
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_stableLattice_integralCharacter : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) {G : Type} [Group G] [TopologicalSpace G]
    (θ : G →* (↥(OL LL))ˣ) (Lc : Lattice (O := ↥(OL LL)) (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) θ))),
    ∃ e : ↥(OL LL) ≃ₗ[↥(OL LL)] ↥Lc.T, ∀ g a, e (Formalism.GaloisCohomology.scalRep (↥(OL LL)) θ g a) = latRep Lc g (e a) := by
  first | exact @GlobalTheory.CharLat.exists_equiv_charLattice | exact GlobalTheory.CharLat.exists_equiv_charLattice | (intros; apply GlobalTheory.CharLat.exists_equiv_charLattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrixStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariantMap_breuilKisinMatrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N N' d d' : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Pre bk N d ρ) (F' : Pre bk N' d' ρ') (f : Matrix (Fin d') (Fin d) (ℤ_[l])), (∀ g, f * ρ g = ρ' g * f) → ∃ Y : Matrix (Fin d') (Fin d) (bk.S), F'.T * Y.map bk.evW = zW f * F.T := by
  first | exact @GlobalTheory.BKLim.EquivKisin.main | exact GlobalTheory.BKLim.EquivKisin.main | (intros; apply GlobalTheory.BKLim.EquivKisin.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisModPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleBasis_modPow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d d' n : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (ρ' : ↥(GK K) →* GL (Fin d') ℤ_[l]) (F' : Pre bk N d' fun g => (ρ' g).val) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), 1 ≤ n → Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (Tn : Matrix (Fin d) (Fin d) (WCb l)) (R : Matrix (Fin d) (Fin d') (WCb l)) (R' : Matrix (Fin d') (Fin d) (WCb l)), IsUnit Tn ∧ (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - Tn * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T * R' - Tn) i j) := by
  first | exact @GlobalTheory.BKLim.etBasis_modPow | exact GlobalTheory.BKLim.etBasis_modPow | (intros; apply GlobalTheory.BKLim.etBasis_modPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProjectiveDescentPrismCoverStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteProjective_descent_prismCover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C), Cover h → ∃ (P : Type) (_ : AddCommGroup P) (_ : Module B.A P) (_ : Module.Finite B.A P) (_ : Module.Projective B.A P) (u : P →ₛₗ[h.f] (Fin d → C.A)), SemiBC u ∧ ∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → ∀ x, (fun i => p.f (u x i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (u x i) := by
  first | exact @GlobalTheory.BSP.CoverDesc.exists_descent | exact GlobalTheory.BSP.CoverDesc.exists_descent | (intros; apply GlobalTheory.BSP.CoverDesc.exists_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixCrystallineModuleOverWitt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SeedF

variable {l : ℕ} [Fact l.Prime]

theorem aw_injective (C : Core l) (a : ℕ) [NeZero a] :
    Function.Injective ((Per.aB l).comp (wA l a).toRingHom) := by
  haveI : Nontrivial (Per.BdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1.nontrivial
  haveI : Nontrivial (Per.Bcris l) := C.ι.domain_nontrivial
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h0
  rw [map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (((l : ℕ) : Per.Bcris l) ^ m * ((Per.aB l).comp (wA l a).toRingHom) (b : Wq l a)) :=
    ((isUnit_l_Bcris l).pow m).mul (b.isUnit.map _)
  exact hu.ne_zero hx

theorem clear_den {d : ℕ} {R : Type} [CommRing R] (f : R →+* Per.Bcris l)
    (G : Matrix (Fin d) (Fin d) (Per.Bcris l))
    (h : ∀ i j, ∃ (n : ℕ) (w : R), ((l : ℕ) : Per.Bcris l) ^ n * G i j = f w) :
    ∃ (k : ℕ) (F : Matrix (Fin d) (Fin d) R), ((l : ℕ) : Per.Bcris l) ^ k • G = F.map f := by
  choose n w hw using h
  refine ⟨Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2),
    Matrix.of fun i j => ((l : ℕ) : R) ^ (Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2) - n i j) * w i j, ?_⟩
  ext i j
  have hle : n i j ≤ Finset.univ.sup (fun p : Fin d × Fin d => n p.1 p.2) :=
    Finset.le_sup (f := fun p : Fin d × Fin d => n p.1 p.2) (Finset.mem_univ (i, j))
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, map_mul, map_pow, map_natCast, smul_eq_mul,
    ← hw]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem inv_entries {K : FinExt l} {d : ℕ} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)) (hUU : U * U' = 1)
    (hρ : ∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) (g : ↥(GK K)) :
    (U' * U.map (Per.φB l)).map (Per.σB (g : GQ l)) = U' * U.map (Per.φB l) ∧
    (U'.map (Per.φB l) * U).map (Per.σB (g : GQ l)) = U'.map (Per.φB l) * U := by
  have hU'U : U' * U = 1 := mul_eq_one_comm.1 hUU
  have hR : (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U := hρ g
  have hσ1 : U.map (Per.σB (g : GQ l)) * U'.map (Per.σB (g : GQ l)) = 1 := by
    rw [← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _)]
  have hσU' : U'.map (Per.σB (g : GQ l)) = U' * (ρ g).map (Per.zB l) := by
    calc U'.map (Per.σB (g : GQ l))
        = (U' * (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l))) * U'.map (Per.σB (g : GQ l)) := by
          rw [mul_assoc U', hR, hU'U, one_mul]
      _ = U' * (ρ g).map (Per.zB l) := by rw [mul_assoc, hσ1, mul_one]
  have hφR : ((ρ g).map (Per.zB l)).map (Per.φB l) = (ρ g).map (Per.zB l) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [GlobalTheory.RingIface.zB_eq_aB_zA, (ActLaws.act_laws l).2.2.2.2.2.2.1, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1]
  have hcomm : ∀ M : Matrix (Fin d) (Fin d) (Per.Bcris l),
      (M.map (Per.φB l)).map (Per.σB (g : GQ l)) = (M.map (Per.σB (g : GQ l))).map (Per.φB l) := by
    intro M
    ext i j
    simp only [Matrix.map_apply]
    exact ((ActLaws.act_laws l).2.2.2.2.1 _ _).symm
  constructor
  · calc (U' * U.map (Per.φB l)).map (Per.σB (g : GQ l))
        = U'.map (Per.σB (g : GQ l)) * (U.map (Per.σB (g : GQ l))).map (Per.φB l) := by
          rw [Matrix.map_mul, hcomm]
      _ = U' * (((ρ g).map (Per.zB l)).map (Per.φB l) * (U.map (Per.σB (g : GQ l))).map (Per.φB l)) := by
          rw [hσU', hφR, mul_assoc]
      _ = U' * U.map (Per.φB l) := by rw [← Matrix.map_mul, hR]
  · calc (U'.map (Per.φB l) * U).map (Per.σB (g : GQ l))
        = (U'.map (Per.σB (g : GQ l))).map (Per.φB l) * U.map (Per.σB (g : GQ l)) := by
          rw [Matrix.map_mul, hcomm]
      _ = U'.map (Per.φB l) * ((ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l))) := by
          rw [hσU', Matrix.map_mul, hφR, mul_assoc]
      _ = U'.map (Per.φB l) * U := by rw [hR]

theorem frob_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvB →
    ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)),
    U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) →
    ∃ (c₁ c₃ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)),
      F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧
      (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
  intro l _ K bk C hC d ρ U U' hUU hρ
  have hU'U : U' * U = 1 := mul_eq_one_comm.1 hUU
  have hent : ∀ G : Matrix (Fin d) (Fin d) (Per.Bcris l), (∀ g : ↥(GK K), G.map (Per.σB (g : GQ l)) = G) →
      ∀ i j, ∃ (n : ℕ) (w : Wq l bk.a),
        ((l : ℕ) : Per.Bcris l) ^ n * G i j = ((Per.aB l).comp (wA l bk.a).toRingHom) w := by
    intro G hG i j
    obtain ⟨x, hxK, hx⟩ := hC K (G i j) fun g hg => by
      have := congrFun (congrFun (hG ⟨g, hg⟩) i) j
      simpa only [Matrix.map_apply] using this
    obtain ⟨n, w, hw⟩ := GlobalTheory.T.exists_pow_mul_unramified_eq_witt_bcris l K bk C x hxK
    exact ⟨n, w, by rw [← hx, hw]; rfl⟩
  obtain ⟨k, F, hF⟩ := clear_den _ _ (hent _ fun g => (inv_entries ρ U U' hUU hρ g).1)
  obtain ⟨k', F', hF'⟩ := clear_den _ _ (hent _ fun g => (inv_entries ρ U U' hUU hρ g).2)
  have hGG : (U' * U.map (Per.φB l)) * (U'.map (Per.φB l) * U) = 1 := by
    rw [mul_assoc, ← mul_assoc (U.map _), ← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _),
      one_mul, hU'U]
  refine ⟨k, k + k', F, F', ?_, ?_⟩
  · apply Matrix.map_injective (aw_injective C bk.a)
    change (F * F').map ((Per.aB l).comp (wA l bk.a).toRingHom) =
      (((l : ℕ) : Wq l bk.a) ^ (k + k') • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a))).map
        ((Per.aB l).comp (wA l bk.a).toRingHom)
    rw [Matrix.map_mul, ← hF, ← hF', Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, hGG]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  · rw [← hF, Matrix.mul_smul, ← mul_assoc, hUU, one_mul]

end GlobalTheory.SeedF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteModuleKilledByPowOfNotIsUnitStatement
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_zero_of_finite_of_not_isUnit : ∀ (O : Type) [CommRing O] [IsLocalRing O] (lam : O), ¬ IsUnit lam →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], ∃ a : ℕ, ∀ x : X, lam ^ a • x = 0 := by
  first | exact @GlobalTheory.finite_module_killed_by_pow_of_not_isUnit | exact GlobalTheory.finite_module_killed_by_pow_of_not_isUnit | (intros; apply GlobalTheory.finite_module_killed_by_pow_of_not_isUnit <;> assumption)
end

