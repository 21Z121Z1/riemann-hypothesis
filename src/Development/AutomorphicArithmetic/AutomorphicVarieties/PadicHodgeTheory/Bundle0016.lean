import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0573
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataComparison
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormSubgroupOpen

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.CharFil

section Generic

open GlobalTheory.SplitJump

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)

private theorem split_fil (a : ℤ) (W W' : Matrix (Fin n) (Fin n) BdR) (hWW : W * W' = 1)
    (hW : ∀ i j, W i j ∈ PD.Fil a) (hW' : ∀ i j, W' i j ∈ PD.Fil (-a))
    (hg : ∀ g, (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)) * W.map (PD.actdR g) = W)
    (y : V ⊗[Qp] BdR) (hy : y ∈ DdR PD ρ) (b : ℤ) :
    (b ≤ a → y ∈ FilV PD (LL := LL) (V := V) b) ∧ (a < b → y ∈ FilV PD (LL := LL) (V := V) b → y = 0) := by
  obtain ⟨k, hk⟩ := exists_coord PD ρ e W W' hWW hg y hy
  have hc : coord e BdR y = W.mulVec fun i => algebraMap K BdR (k i) := by
    rw [hk, Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]
  refine ⟨fun hb => ?_, fun hb hF => ?_⟩
  · rw [mem_filV PD e]
    intro i
    rw [hc]
    refine fil_mono PD hb ?_
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [mul_comm, ← Algebra.smul_def]
    exact (PD.Fil a).smul_mem _ (hW i j)
  · rw [mem_filV PD e] at hF
    have hk0 : ∀ i, k i = 0 := fun i => by
      refine eq_zero_of_mem_fil_one PD _ ?_
      rw [congrFun hk i]
      simp only [Matrix.mulVec, dotProduct]
      refine Submodule.sum_mem _ fun j _ => ?_
      exact fil_mono PD (by omega) (PD.Fil_mul _ _ _ _ (hW' i j) (hF j))
    apply (coord e BdR).injective
    rw [hc, map_zero]
    funext i
    simp [hk0, Matrix.mulVec, dotProduct]

end Generic

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E]

private theorem val_integral {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] (μ : G →* Eˣ)
    (hμ : Continuous fun g => (μ g : E)) (g : G) : IsIntegral ℤ_[l] (μ g : E) := by
  let j : E →ₐ[ℚ_[l]] Om l := IsAlgClosed.lift
  have hj : Continuous j := IsModuleTopology.continuous_of_linearMap j.toLinearMap
  let d : G →* Om l := (j : E →* Om l).comp ((Units.coeHom E).comp μ)
  have hd : ‖d g‖ = 1 := GlobalTheory.UnramifiedChar.norm_eq_one_of_compact d (hj.comp hμ) g
  let LL : FinExt l := ⟨j.fieldRange, Module.Finite.of_surjective j.rangeRestrict.toLinearMap j.rangeRestrict_surjective⟩
  have h1 : (⟨j (μ g), ⟨_, rfl⟩⟩ : ↥LL.1) ∈ OL LL := (GlobalTheory.Per.Val.mem_OL_iff LL _).2 hd.le
  have h2 : IsIntegral ℤ_[l] (j (μ g)) := IsIntegral.map (LL.1.val.restrictScalars ℤ_[l]) h1
  exact (isIntegral_algHom_iff (j.restrictScalars ℤ_[l]) j.injective).1 h2

omit [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] in

private theorem exists_int_basis : ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] E),
    ∀ x : E, IsIntegral ℤ_[l] x ↔ ∀ i, ‖e.repr x i‖ ≤ 1 := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  have : IsTorsionFree ℤ_[l] E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  have : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] E) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] E _
  have : Module.Free ℤ_[l] ↥(integralClosure ℤ_[l] E) := IsIntegralClosure.module_free ℤ_[l] ℚ_[l] E _
  have : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] E).toSubmodule := ‹Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] E)›
  have : Module.Free ℤ_[l] ↥(integralClosure ℤ_[l] E).toSubmodule := ‹Module.Free ℤ_[l] ↥(integralClosure ℤ_[l] E)›
  refine GlobalTheory.Cyc.LatBasis.exists_basis_of_submodule (integralClosure ℤ_[l] E).toSubmodule fun x => ?_
  have hx : IsAlgebraic ℤ_[l] x := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  exact hx.exists_integral_multiple

open GlobalTheory.UnramifiedCrys GlobalTheory.UnramifiedRep in

private theorem exists_split [IsTopologicalRing E] (K : FinExt l) (μ : ↥(GK K) →* Eˣ)
    (hμ : Continuous fun g => (μ g : E)) (hI : ∀ g ∈ IK K, μ g = 1) :
    ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] E) (W W' : Matrix (Fin n) (Fin n) (Bdr l)), W * W' = 1 ∧
      (∀ i j, W i j ∈ ((PP l).PD K).Fil 0) ∧ (∀ i j, W' i j ∈ ((PP l).PD K).Fil 0) ∧
      ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] (Bdr l) (e.repr (chRep μ g (e j)) i)) *
        W.map (((PP l).PD K).actdR g) = W := by
  have := compactSpace_GK K
  obtain ⟨Ti⟩ := tiedP l
  set P := PP l
  set AI := AIP l
  obtain ⟨n, e, he⟩ := exists_int_basis (l := l) (E := E)
  have hρ : ∀ g x, chRep μ g x = (μ g : E) * x := fun _ _ => rfl
  have hint : ∀ g i j, ‖e.repr (chRep μ g (e j)) i‖ ≤ 1 := fun g i j =>
    (he _).1 ((val_integral μ hμ g).mul ((he (e j)).2 fun k => by
      rw [e.repr_self, Finsupp.single_apply]
      split_ifs <;> simp)) i
  obtain ⟨M, hM⟩ := exists_matrixHom (chRep μ) e hint
  obtain ⟨W, hW, hWg⟩ := exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)) M
    (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by
      have h := (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hμ.mul (continuous_const (y := e j)))
      exact h.congr fun g => (hM g i j).symm))
    (fun g hg => by
      have h := hI g (Subgroup.subset_closure fun x hx =>
        norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)
      rw [← map_one M]
      ext i j
      apply PadicInt.ext
      rw [hM, hM, hρ, hρ, h, map_one])
  have hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (chRep μ g (e j)) i)) *
      (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W := fun g => by
    conv_rhs => rw [← hWg g, map_mul]
    congr 1
    · ext i j
      rw [Matrix.of_apply, ← hM]
      exact (ιA_zlW AI Ti (M g i j)).symm
    · ext i j
      exact (P.PD_actB K g _).trans (AI.ιA_act g _).symm
  let f : Ainf l →+* P.R.BdR := ((P.PD K).ι : P.R.B →+* P.R.BdR).comp AI.ιA
  have hf : ∀ a, f a ∈ (P.PD K).Fil 0 := fun a => by
    change (P.PD K).ι (AI.ιA a) ∈ _
    rw [P.PD_ι]
    exact AI.ainf_image_mem_filtration_zero K a
  refine ⟨n, e, f.mapMatrix W, f.mapMatrix W⁻¹, ?_, fun i j => hf _, fun i j => hf _, fun g => ?_⟩
  · rw [← map_mul, Matrix.mul_nonsing_inv _ hW, map_one]
  · have hι : ∀ c : ℚ_[l], ((P.PD K).ι : P.R.B →+* P.R.BdR) (algebraMap ℚ_[l] P.R.B c) =
        algebraMap ℚ_[l] P.R.BdR c := fun c => (P.PD_ι K _).trans (P.ιB.commutes c)
    exact map_mul_map_eq ((P.PD K).ι : P.R.B →+* P.R.BdR) (hB g) (fun i j => hι _)
      ((P.PD K).ι_comm g)

omit [FiniteDimensional ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] in
private theorem cycA_val (g : GQ l) : cycA l l E g = Units.map (algebraMap ℚ_[l] E : ℚ_[l] →* E) ((PP l).χQ g) := by
  ext
  change algebraMap ℤ_[l] E _ = algebraMap ℚ_[l] E _
  rw [(cycFacts l l).2.2 g, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E]
  rfl

omit [FiniteDimensional ℚ_[l] E] in
private theorem cont_cycA [IsTopologicalRing E] (w : ℤ) : Continuous fun g : GQ l => ((cycA l l E g ^ w : Eˣ) : E) := by
  have h1 : Continuous (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] E)).comp continuous_subtype_val
  have h2 : Continuous fun g : GQ l => cyc l l g ^ w := (cycFacts l l).1.zpow w
  refine (h1.comp (Units.continuous_val.comp h2)).congr fun g => ?_
  exact congrArg Units.val (map_zpow (Units.map (algebraMap ℤ_[l] E : ℤ_[l] →* E)) (cyc l l g) w)

private theorem gk_case [IsTopologicalRing E] (K : FinExt l) (κ : ↥(GK K) →* Eˣ)
    (hκ : Continuous fun g => (κ g : E)) (w : ℤ) (hI : ∀ g ∈ IK K, κ g = cycA l l E g ^ w)
    (y : E ⊗[ℚ_[l]] Bdr l) (hy : y ∈ DdR ((PP l).PD K) (chRep κ)) (b : ℤ) :
    (b ≤ -w → y ∈ FilV ((PP l).PD K) (LL := E) (V := E) b) ∧
      (-w < b → y ∈ FilV ((PP l).PD K) (LL := E) (V := E) b → y = 0) := by
  obtain ⟨T⟩ := tiedP l
  let μ : ↥(GK K) →* Eˣ := κ * ((cycA l l E).comp (GK K).subtype) ^ (-w)
  have hμ : ∀ g, μ g = κ g * cycA l l E g ^ (-w) := fun _ => rfl
  obtain ⟨n, e, W, W', hWW, hW, hW', hg⟩ := exists_split K μ
    (hκ.mul ((cont_cycA (-w)).comp continuous_subtype_val))
    (fun g hg => by rw [hμ, hI g hg, zpow_neg, mul_inv_cancel])
  set t := GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR (PP l) K
  have ht : (t : Bdr l) = ((PP l).PD K).ι ((PP l).PD K).t := rfl
  refine split_fil ((PP l).PD K) (chRep κ) e (-w) (((t ^ (-w) : (Bdr l)ˣ) : Bdr l) • W)
    (((t ^ w : (Bdr l)ˣ) : Bdr l) • W') ?_ (fun i j => ?_) (fun i j => ?_) (fun g => ?_) y hy b
  · rw [Matrix.smul_mul, Matrix.mul_smul, hWW, smul_smul, zpow_neg, Units.inv_mul, one_smul]
  · simpa using ((PP l).PD K).Fil_mul _ _ _ _ (GlobalTheory.DRFil.tdR_zpow_mem T K (-w)) (hW i j)
  · simpa using ((PP l).PD K).Fil_mul _ _ _ _ (GlobalTheory.DRFil.tdR_zpow_mem T K w) (hW' i j)
  · conv_rhs => rw [← hg g]
    ext i j
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, smul_eq_mul, map_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hχ : ((PP l).PD K).χ g = (PP l).χQ g := Units.ext ((PP l).PD_χ K g)
    have h1 : chRep μ g (e k) = (((PP l).χQ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) • chRep κ g (e k) := by
      change (μ g : E) * e k = _ • ((κ g : E) * e k)
      rw [hμ, cycA_val, ← map_zpow, Algebra.smul_def, Units.val_mul, Units.coe_map]
      simp only [MonoidHom.coe_coe]
      ring
    rw [GlobalTheory.DRDual.act_zpow _ t ht, hχ, h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]
    ring

end UpperTheory.V.Loc.CharFil

open UpperTheory.V.Loc.CharFil in
theorem UpperTheory.V.Loc.charFil :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (κ : G →* Eˣ), Continuous (fun g => (κ g : E)) → ∀ w : ℤ, HasWeight φ κ w → IsDr φ (chRep κ) ∧ ∀ i : ℤ, (i ≤ -w → FilD φ (chRep κ) i = Ddr φ (chRep κ)) ∧ (-w < i → FilD φ (chRep κ) i = ⊥) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ κ hκ w ⟨U, hU, hw⟩
  have hφU : IsOpenEmbedding (φ.comp U.subtype) := hφ.comp hU.isOpenEmbedding_subtypeVal
  have hc : ContAction (chRep κ) := (hκ.comp continuous_fst).mul continuous_snd
  have hcU : ContAction ((chRep κ).comp U.subtype : Representation E U E) :=
    (hκ.comp (continuous_subtype_val.comp continuous_fst)).mul continuous_snd
  refine ⟨((isCrys_isDR_restrict_openSubgroup φ hφ _ hc).2 U hU).2.2 ((isCrys_isDR_restrict_openSubgroup _ hφU _ hcU).1 (crUnr _ hφU _ hcU w fun g hg x => ?_)),
    fun i => ?_⟩
  · change (κ g : E) • x = _
    rw [hw g g.2 hg]
    rfl
  obtain ⟨K, e, -, he, hf, -, -, -⟩ := openField _ hφU
  have hf' : ∀ g : ↥(GK K), φ (e.symm g) = g := fun g => by
    have := DFunLike.congr_fun hf (e.symm g)
    simpa using this.symm
  let κ' : ↥(GK K) →* Eˣ := (κ.comp U.subtype).comp e.symm.toMonoidHom
  have hF : FilT E E i = FilV ((PP l).PD K) (LL := E) (V := E) i := by
    have : (((PP l).PD (botExt l)).Fil i).restrictScalars ℚ_[l] = (((PP l).PD K).Fil i).restrictScalars ℚ_[l] :=
      SetLike.coe_injective ((PP l).PD_Fil _ _ i)
    unfold FilT FilV
    rw [this]
  have key : ∀ y ∈ Ddr φ (chRep κ), (i ≤ -w → y ∈ FilT E E i) ∧ (-w < i → y ∈ FilT E E i → y = 0) := by
    intro y hy
    rw [hF]
    refine gk_case K κ' (hκ.comp (continuous_subtype_val.comp he)) w (fun g hg => ?_) y ?_ i
    · have := hw (e.symm g) (e.symm g).2 (by rw [hf']; exact (memIK K g).1 hg)
      rw [hf'] at this
      exact this
    · refine (Submodule.mem_iInf _).2 fun g => ?_
      have h1 := (Submodule.mem_iInf _).1 hy (e.symm g)
      have h2 : actVdR ((PP l).PD K) (chRep κ') g = actD φ (chRep κ) (e.symm g) := by
        unfold actVdR actD
        rw [hf']
        congr 1
        exact LinearMap.ext fun z => (PP l).PD_actdR K g z
      rw [h2]
      exact h1
  exact ⟨fun h => inf_eq_left.2 fun y hy => (key y hy).1 h,
    fun h => (Submodule.eq_bot_iff _).2 fun y hy => (key y hy.1).2 h hy.2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CompKer
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

theorem UpperTheory.V.Loc.compKer :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (Pc : Cond O rbar) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R), Represents Pc ρ → ∀ (x : R →ₐ[O] O) (P : Ideal R) {n : ℕ} (φ : R →ₐ[O] MvPowerSeries (Fin n) E), UpperTheory.V.Loc.IsCompl P x φ → (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : R →ₐ[O] C), OnComp Pc (ρ.map x).hom (ρ.map f) ↔ P ≤ RingHom.ker f := by
  intro l _ O _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ Γ ι _ _ _ _ rbar Pc R _ _ _ ρ hR x P n φ hc hy0 C _ _ _ f
  have hcomp : ∀ {A B D : Type} [CommRing A] [Algebra O A] [IsCO O A] [CommRing B] [Algebra O B] [IsCO O B]
      [CommRing D] [Algebra O D] [IsCO O D] (u : A →ₐ[O] B) (v : B →ₐ[O] D) (r : Lift O rbar A),
      Lift.map v (Lift.map u r) = Lift.map (v.comp u) r := by
    intro A B D _ _ _ _ _ _ _ _ _ u v r
    apply Lift.ext
    ext γ a b
    rfl
  constructor
  · rintro ⟨B, _, _, _, _, ρB, hPB, ⟨x4, hx4⟩, y, hy⟩
    obtain ⟨g, hg, -⟩ := (hR B).2 ρB hPB
    subst hg
    have hf : y.comp g = f := by
      obtain ⟨h, -, huniq⟩ := (hR C).2 (Lift.map f ρ) ((hR C).1 f)
      rw [huniq (y.comp g) (by show Lift.map (y.comp g) ρ = _; rw [← hcomp]; exact hy), huniq f rfl]
    have hx : x4.comp g = x := by
      obtain ⟨h, -, huniq⟩ := (hR O).2 (Lift.map x ρ) ((hR O).1 x)
      refine (huniq (x4.comp g) ?_).trans (huniq x rfl).symm
      show Lift.map (x4.comp g) ρ = _
      rw [← hcomp]
      apply Lift.ext
      ext γ a b
      exact hx4 γ a b
    obtain ⟨y0, hy0ne, hann⟩ := hy0
    intro a ha
    rw [RingHom.mem_ker, ← hf]
    have hprod : g y0 * g a = 0 := by rw [← map_mul, hann a ha, map_zero]
    rcases mul_eq_zero.1 hprod with h0 | h0
    · exfalso
      apply hy0ne
      rw [← hx]
      simp [h0]
    · simp [h0]
  · intro hPf
    haveI : IsDomain (MvPowerSeries (Fin n) E) := NoZeroDivisors.to_isDomain _
    have hker : RingHom.ker φ = P := hc.ker
    haveI hprime : P.IsPrime := hker ▸ RingHom.ker_isPrime φ
    have hxP : ∀ a ∈ P, x a = 0 := by
      intro a ha
      have h1 := hc.const a
      rw [← hker, RingHom.mem_ker] at ha
      rw [ha, map_zero] at h1
      exact (IsFractionRing.injective O E) (by rw [← h1, map_zero])
    have hfP : ∀ a ∈ P, f a = 0 := fun a ha => (RingHom.mem_ker).1 (hPf ha)
    letI hco : IsCO O (R ⧸ P) :=
      co_quot O R (R ⧸ P) (Ideal.Quotient.mkₐ O P) (Ideal.Quotient.mkₐ_surjective O P)
    refine ⟨R ⧸ P, inferInstance, inferInstance, hco, inferInstance,
      Lift.map (Ideal.Quotient.mkₐ O P) ρ, (hR _).1 _, ⟨Ideal.Quotient.liftₐ P x hxP, ?_⟩,
      ⟨Ideal.Quotient.liftₐ P f hfP, ?_⟩⟩
    · intro γ a b
      rfl
    · rw [hcomp]
      apply Lift.ext
      ext γ a b
      rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ContinuousUnitsInvOfContinuousCoeFiniteQpAlgebra
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.continuous_units_inv_of_continuous_coe_finite_Qp_algebra :
    ∀ {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] {X : Type} [TopologicalSpace X] (f : X → Bˣ), Continuous (fun x => (f x : B)) → Continuous fun x => (((f x)⁻¹ : Bˣ) : B) := by
  intro l _ B _ _ _ _ _ _ X _ f hf
  classical
  let b := Module.finBasis ℚ_[l] B
  let M := Algebra.leftMulMatrix b
  let E : (Fin (Module.finrank ℚ_[l] B) → ℚ_[l]) →ₗ[ℚ_[l]] B := b.equivFun.symm.toLinearMap
  have key : ∀ u : Bˣ, ((u⁻¹ : Bˣ) : B) = E (Matrix.mulVec (M (u : B))⁻¹ (b.repr 1)) := by
    intro u
    have hinv : (M (u : B))⁻¹ = M ((u⁻¹ : Bˣ) : B) := by
      apply Matrix.inv_eq_left_inv
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hinv, Algebra.leftMulMatrix_mulVec_repr, mul_one]
    simp [E]
  have hM : Continuous fun y : B => M y :=
    IsModuleTopology.continuous_of_linearMap M.toLinearMap
  have hE : Continuous E := LinearMap.continuous_on_pi E
  have hcomp : Continuous fun x => E (Matrix.mulVec (M (f x : B))⁻¹ (b.repr 1)) := by
    refine hE.comp ?_
    refine Continuous.matrix_mulVec ?_ continuous_const
    rw [continuous_iff_continuousAt]
    intro x
    refine ContinuousAt.comp (f := fun x => M (f x : B)) (g := Inv.inv) ?_ (hM.comp hf).continuousAt
    apply continuousAt_matrix_inv
    have hdet : IsUnit (M (f x : B)).det := by
      have : IsUnit (M (f x : B)) := (f x).isUnit.map M
      exact (Matrix.isUnit_iff_isUnit_det _).1 this
    obtain ⟨d, hd⟩ := hdet
    rw [← hd]
    exact NormedRing.inverse_continuousAt d
  simpa only [← key] using hcomp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsAlgebraicElementOfAlgebraicVectorSubspace
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial
open GlobalTheory.UnramifiedCrys

private def algSub (p : ℕ) [hp : Fact p.Prime] (R : Type) [CommRing R] [CharP R p] : Subring R where
  carrier := {y | ∃ m, 0 < m ∧ y ^ p ^ m = y}
  one_mem' := ⟨1, one_pos, one_pow _⟩
  zero_mem' := ⟨1, one_pos, zero_pow (pow_pos hp.out.pos _).ne'⟩
  mul_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [mul_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [add_pow_char_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  neg_mem' := by
    rintro x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    have h := sub_pow_char_pow (p := p) (n := a) (0 : R) x
    rwa [zero_sub, hx, zero_pow (pow_pos hp.out.pos _).ne', zero_sub] at h

private theorem exists_alg {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    (ρ : G →* (R ≃+* R)) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      ∀ g (f : R →+* R), (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → f y = ρ g y) →
        (M g).map (zlW p R) * W.map (WittVector.map f) = W :=
  _root_.UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg ρ hopen M hM hJ

theorem UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ_[l]), IsUnit C.det → ∃ N N' : Matrix (Fin n) (Fin n) (Bcr l), N * N' = 1 ∧ (∀ i j, (PP l).ιB (N i j) ∈ ((PP l).PD (botExt l)).Fil 0) ∧ (∀ i j, (PP l).ιB (N' i j) ∈ ((PP l).PD (botExt l)).Fil 0) ∧ N.map (PP l).φB = C.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l])) * N ∧ ∀ g ∈ Iq l, N.map ((PP l).actQ g) = N := by
  intro l _ n C hC
  obtain ⟨-, -, hI, ⟨σ, hσ⟩, -⟩ := iqBasic l
  obtain ⟨Ti⟩ := tiedP l
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det C).2 hC
  haveI : CompactSpace (Matrix (Fin n) (Fin n) ℤ_[l]) := inferInstanceAs (CompactSpace (Fin n → Fin n → ℤ_[l]))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) ℤ_[l]) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → ℤ_[l]))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) ℤ_[l])ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℤ_[l])).symm.isEmbedding.isTotallyDisconnected_range.1
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) ℤ_[l])ˣ :=
    Units.isEmbedding_embedProduct.isTotallyDisconnected_range.1
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  obtain ⟨f, hf, hfI, hfσ⟩ := frobFree σ hσ (Matrix (Fin n) (Fin n) ℤ_[l])ˣ u⁻¹
  obtain ⟨W, hW, hWg⟩ := exists_alg (p := l) (AIP l).actT (eventually_actT_eq (AIP l))
    ((Units.coeHom _).comp f) (Units.continuous_val.comp hf)
    (fun g hg => congrArg Units.val (hfI g ((hI g).2 (norm_sub_lt_one_of_fix (AIP l) g hg))))
  refine ⟨(AIP l).ιA.mapMatrix W, (AIP l).ιA.mapMatrix W⁻¹, ?_, fun i j => (AIP l).ainf_image_mem_filtration_zero _ _,
    fun i j => (AIP l).ainf_image_mem_filtration_zero _ _, ?_, fun g hg => ?_⟩
  · rw [← map_mul, Matrix.mul_nonsing_inv _ hW, map_one]
  · have h := hWg σ (frobenius _ l) fun m hm y hy => ((UpperTheory.tilt_frobenius_action_pow_and_inertia_trivial_of_pow_eq_self y m hm hy).1 σ hσ).symm
    have h1 : W.map (WittVector.map (frobenius _ l)) = (zlW l (OCb l)).mapMatrix u * W := by
      conv_rhs => rw [← h, ← Matrix.mul_assoc]
      have e : (((Units.coeHom _).comp f) σ).map (zlW l (OCb l)) = (zlW l (OCb l)).mapMatrix (↑u⁻¹) := by
        rw [← hfσ]; rfl
      rw [e, ← map_mul, Units.mul_inv, map_one, Matrix.one_mul]
    have h2 := congrArg (AIP l).ιA.mapMatrix h1
    rw [map_mul] at h2
    convert h2 using 1
    · ext i j
      change (PP l).φB ((AIP l).ιA (W i j)) = (AIP l).ιA (WittVector.map (frobenius _ l) (W i j))
      rw [← (AIP l).ιA_φ, WittVector.frobenius_eq_map_frobenius]
    · congr 1
      ext i j
      exact (ιA_zlW (AIP l) Ti _).symm
  · have h := hWg 1 ((AIP l).actT g).toRingHom fun m hm y hy => by
      rw [map_one, RingAut.one_apply]
      exact (UpperTheory.tilt_frobenius_action_pow_and_inertia_trivial_of_pow_eq_self y m hm hy).2 g hg
    rw [map_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul] at h
    ext i j
    change (PP l).actQ g ((AIP l).ιA (W i j)) = (AIP l).ιA (W i j)
    rw [← (AIP l).ιA_act]
    exact congrArg (AIP l).ιA (congrFun (congrFun h i) j)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCocycleExtensionOfConjugationInvariantRest
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem zm_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out⁻¹ * (g * q.out) ∈ H := by
  rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rfl

private noncomputable def zm_h {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) : H :=
  ⟨(g • q).out⁻¹ * (g * q.out), zm_mem H g q⟩

private theorem zm_h_mul {G : Type} [Group G] (H : Subgroup G) (g g' : G) (q : G ⧸ H) :
    zm_h H (g * g') q = zm_h H g (g' • q) * zm_h H g' q := by
  apply Subtype.ext
  simp only [zm_h, Subgroup.coe_mul, mul_smul]
  group

private theorem zm_out {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out * (zm_h H g q : G) = g * q.out := by
  simp only [zm_h]
  group

private theorem zm_fix {G : Type} [Group G] (H : Subgroup G) [hN : H.Normal] (h : H) (q : G ⧸ H) :
    (h : G) • q = q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, eq_comm, QuotientGroup.eq]
    have := hN.conj_mem _ h.2 x⁻¹
    simpa [mul_assoc] using this

private theorem zm_sum {G : Type} [Group G] (H : Subgroup G) [Fintype (G ⧸ H)] {V : Type} [AddCommGroup V]
    (g : G) (f : G ⧸ H → V) : ∑ q, f (g • q) = ∑ q, f q :=
  Equiv.sum_comp (MulAction.toPerm g) f

private theorem zm_cont {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (q : G ⧸ H) : Continuous fun g : G => (g • q).out := by
  haveI : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  have h1 : Continuous fun g : G => g • q := by fun_prop
  exact (continuous_of_discreteTopology (f := fun x : G ⧸ H => x.out)).comp h1

theorem UpperTheory.exists_cocycle_extension_of_conjugation_invariant_restriction :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → ∀ (H : Subgroup G) [H.Normal] [H.FiniteIndex], IsOpen (H : Set G) → ∀ (N : Submodule A (H → V)), ∀ c ∈ Z1 (ρ.comp H.subtype : Representation A H V), (∀ (s : G) (c' : H → V), (∀ g g' : H, (g' : G) = s⁻¹ * g * s → c' g = ρ s (c g')) → c' - c ∈ N) → ∃ b ∈ Z1 ρ, (fun g : H => b g) - c ∈ N := by
  intro l _ G _ _ _ A _ _ V _ _ _ _ _ _ _ _ _ ρ hρ H hHN _ hH N c hc hs
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set n : ℕ := Fintype.card (G ⧸ H) with hn
  have hn0 : (n : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  obtain ⟨a, ha⟩ : ∃ a : A, ∀ x : V, a • (n • x) = x :=
    ⟨algebraMap ℚ_[l] A (n : ℚ_[l])⁻¹, fun x => by
      rw [algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, inv_mul_cancel₀ hn0, one_smul]⟩
  have hmul : ∀ g g' x, ρ g (ρ g' x) = ρ (g * g') x := fun g g' x => by
    rw [map_mul, Module.End.mul_apply]
  rw [mem_Z1_iff_cocycle] at hc
  have hc2 : ∀ h h' : H, c (h * h') = c h + ρ h (c h') := hc.2
  let cor : G → V := fun g => ∑ q : G ⧸ H, ρ (g • q).out (c (zm_h H g q))
  have hcor : cor ∈ Z1 ρ := by
    refine ⟨continuous_finset_sum _ fun q _ => ?_, fun g g' => ?_⟩
    · have h1 := zm_cont H hH q
      have h2 : Continuous fun g : G => zm_h H g q :=
        Continuous.subtype_mk (h1.inv.mul (continuous_id.mul continuous_const)) _
      exact hρ.comp (h1.prodMk (hc.1.comp h2))
    · simp only [cor]
      rw [← zm_sum H g' (fun q => ρ (g • q).out (c (zm_h H g q))), map_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [zm_h_mul, hc2, map_add, hmul, hmul, mul_smul, zm_out]
  let c' : G ⧸ H → H → V := fun q h => ρ q.out (c (zm_h H h q))
  have hc' : ∀ q, c' q - c ∈ N := fun q => hs q.out (c' q) fun g g' hg => by
    have : zm_h H g q = g' := by
      apply Subtype.ext
      simp only [zm_h, zm_fix, hg, mul_assoc]
    simp only [c', this]
  refine ⟨a • cor, (Z1 ρ).smul_mem a hcor, ?_⟩
  have e : (fun g : H => (a • cor) g) - c = a • ∑ q : G ⧸ H, (c' q - c) := by
    funext h
    have e1 : cor h = ∑ q : G ⧸ H, c' q h := by
      simp only [cor, c', zm_fix]
    simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, e1, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, ← hn, smul_sub, ha]
  rw [e]
  exact N.smul_mem a (N.sum_mem fun q _ => hc' q)
end

