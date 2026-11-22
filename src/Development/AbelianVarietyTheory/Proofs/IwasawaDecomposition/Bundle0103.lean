import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0180
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0075
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalRingCardinality.Lemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host nonZeroDivisors

namespace GlobalTheory.HeckeProduct

section Comp
variable (L : Type) [Field L] [NumberField L]

theorem localIdele_snd_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) v = x
  convert Pi.mulSingle_eq_same v (x : v.adicCompletion L)

theorem localIdele_snd_ne (v w : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) w = 1
  convert Pi.mulSingle_eq_of_ne h (x : v.adicCompletion L)

theorem localIdele_fst (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := rfl

theorem infIdele_fst_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 w = x := by
  classical
  show (Pi.mulSingle w (x : w.Completion) : ∀ u : InfinitePlace L, u.Completion) w = x
  convert Pi.mulSingle_eq_same w (x : w.Completion)

theorem infIdele_fst_ne (w u : InfinitePlace L) (h : u ≠ w) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 u = 1 := by
  classical
  show (Pi.mulSingle w (x : w.Completion) : ∀ u : InfinitePlace L, u.Completion) u = 1
  convert Pi.mulSingle_eq_of_ne h (x : w.Completion)

end Comp

section Parts
variable (F : Type) [Field F] [NumberField F]

def infPart : Ideles F →* (InfiniteAdeleRing F)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def finPart : Ideles F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

variable {F}

theorem infDiag_parts (k : Fˣ) : infPart F (infDiag k) = infPart F (diagUnits F k) ∧ finPart F (infDiag k) = 1 := by
  classical
  constructor
  · apply Units.ext
    funext w
    rw [infDiag, MonoidHom.finset_prod_apply, map_prod, Units.coe_prod]
    have e : (∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) : (InfiniteAdeleRing F)ˣ) :
        InfiniteAdeleRing F)) w = ∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) :
          (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w := Finset.prod_apply _ _ _
    rw [e, Finset.prod_eq_single w]
    · exact infIdele_fst_self F w _
    · intro u _ hu
      exact infIdele_fst_ne F u w (Ne.symm hu) _
    · simp
  · rw [infDiag, MonoidHom.finset_prod_apply, map_prod]
    exact Finset.prod_eq_one fun u _ => Units.ext rfl

end Parts

section Product

variable {F : Type} [Field F] [NumberField F]

open Classical in

def cut (a : FiniteAdeleRing (𝓞 F) F) (T : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then a v else 1, by
    refine Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    apply hw
    have h' : w ∉ T := h
    simp only [h', if_false]
    exact one_mem _⟩

theorem tendsto_cut (a : FiniteAdeleRing (𝓞 F) F) : Filter.Tendsto (cut a) Filter.atTop (nhds a) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | a v ∈ v.adicCompletionIntegers F}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal S)
  let f : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T => ⟨fun v => if v ∈ T then a v else 1, by
    rw [Filter.eventually_principal]
    intro w hw
    by_cases h : w ∈ T
    · simp only [h, if_true]; exact hw
    · simp only [h, if_false]; exact one_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = if v ∈ T then a v else 1
    rw [if_pos this]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf

theorem prod_local (k : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F) =
      (((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).1, cut ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).2 T) := by
  classical
  refine Prod.ext ?_ ?_
  · change ((infPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = _
    have e : ∏ v ∈ T, infPart F (localIdele F v (atFin v k)) = 1 := Finset.prod_eq_one (fun v _ => Units.ext rfl)
    rw [map_mul, map_prod, (infDiag_parts k).1, e, mul_one]
    rfl
  · change ((finPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = _
    rw [map_mul, (infDiag_parts k).2, one_mul]
    induction T using Finset.induction_on with
    | empty => rw [Finset.prod_empty, map_one]; exact Subtype.ext (funext fun v => by simp [cut]; rfl)
    | insert u T hu ih =>
      rw [Finset.prod_insert hu, map_mul, Units.val_mul, ih]
      refine Subtype.ext (funext fun v => ?_)
      change ((localIdele F u (atFin u k) : Ideles F) : AdeleRing (𝓞 F) F).2 v * (if v ∈ T then _ else 1) =
        if v ∈ insert u T then _ else 1
      by_cases h : v = u
      · subst h
        rw [localIdele_snd_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one]; rfl
      · rw [localIdele_snd_ne F u v h, one_mul]; simp [h]

theorem tendsto_prod_local (k : Fˣ) :
    Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
      Filter.atTop (nhds (diagUnits F k)) := by
  have h : ∀ k : Fˣ, Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F))
      Filter.atTop (nhds ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F)) := fun k => by
    simp only [prod_local]
    exact tendsto_const_nhds.prodMk_nhds (tendsto_cut _)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h k).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h k⁻¹
  simp only [map_inv, Finset.prod_inv_distrib, ← mul_inv] at h2
  exact h2

theorem locK_unr (χ : HChar F) {v : HeightOneSpectrum (𝓞 F)} (h : χ.UnrAt v) (k : Fˣ) :
    χ.locK v k = χ.val v ^ ordF v k := by
  have hu : IsUnitAt v (atFin v (k * (unif v ^ ordF v k)⁻¹)) := by
    have h2 := unif_spec v
    have hk : Valued.v ((atFin v k : (v.adicCompletion F)ˣ) : v.adicCompletion F) = v.valuation F (k : F) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)
    have h0 : v.valuation F (k : F) ≠ 0 := by simp
    unfold IsUnitAt IsUnifAt at *
    rw [map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h2, hk, ← WithZero.exp_zsmul, ordF]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
    rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
  have h3 : χ.locK v (k * (unif v ^ ordF v k)⁻¹) = 1 := h _ hu
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
  exact h3

theorem finite_ordF (k : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordF v k ≠ 0}.Finite := by
  have h := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (FiniteAdeleRing.unitEmbedding (𝓞 F) F k))
  refine h.subset fun v hv h0 => hv ?_
  have hk : Valued.v (((FiniteAdeleRing.unitEmbedding (𝓞 F) F k : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) v) = v.valuation F (k : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)
  rw [GlobalTheory.Idele.ord_vw, hk] at h0
  exact h0

theorem productRule (χ : HChar F) : χ.ProductRule := by
  classical
  intro S hS k
  have h1 := (χ.2.1.tendsto _).comp (tendsto_prod_local k)
  rw [χ.2.2 k] at h1
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h1
  filter_upwards [Filter.eventually_ge_atTop (S ∪ (finite_ordF k).toFinset)] with T hT
  have hST : S ⊆ T := Finset.subset_union_left.trans hT
  change _ = χ.1 (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
  rw [map_mul, map_prod, mul_assoc, ← Finset.prod_sdiff hST, mul_comm (∏ v ∈ T \ S, _)]
  refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) rfl ?_)
  rw [finprod_cond_eq_prod_of_cond_iff (fun v => χ.val v ^ ordF v k) (p := fun v => v ∉ S) (t := T \ S)]
  · exact Finset.prod_congr rfl fun v hv => (locK_unr χ (hS v (Finset.mem_sdiff.1 hv).2) k).symm
  · intro v hv
    rw [Finset.mem_sdiff]
    refine ⟨fun h => ⟨hT (Finset.mem_union_right _ ?_), h⟩, fun h => h.2⟩
    rw [Set.Finite.mem_toFinset]
    intro h0
    exact hv (by rw [h0, zpow_zero])

end Product

theorem hchar_productRule : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), χ.ProductRule :=
  fun _ _ _ χ => productRule χ

end GlobalTheory.HeckeProduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemClosureMulVOfFinrankEq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Pst

theorem semilinear_coord_fixed {F D ι : Type*} [Field F] [AddCommGroup D] [Module F D] [Fintype ι]
    {b : ι → D} (hb : LinearIndependent F b) (σ : F → F) (T : D →+ D)
    (hT : ∀ c x, T (c • x) = σ c • T x) (hTb : ∀ i, T (b i) = b i) (c : ι → F)
    (h : T (∑ i, c i • b i) = ∑ i, c i • b i) (i : ι) : σ (c i) = c i := by
  rw [map_sum] at h
  simp only [hT, hTb] at h
  exact Fintype.linearIndependent_iffₛ.mp hb _ _ h i

variable {l : ℕ} [Fact l.Prime]

theorem galois_mem_Kur (g : GQ l) (c : ↥(MaximalUnramifiedExtension l)) : g (c : Om l) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨c, hc⟩ := c
  change g c ∈ MaximalUnramifiedExtension l
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, h0, hm, hx⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨m, h0, hm, by rw [← map_pow, hx, map_one]⟩
  | algebraMap x => rw [g.commutes]; exact (MaximalUnramifiedExtension l).algebraMap_mem x
  | add x y _ _ hx hy => rw [map_add]; exact (MaximalUnramifiedExtension l).add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact (MaximalUnramifiedExtension l).inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact (MaximalUnramifiedExtension l).mul_mem hx hy

theorem mem_of_GK_fixed {K : FinExt l} {x : Om l} (hx : ∀ g : ↥(GK K), (g : GQ l) x = x) : x ∈ K.1 := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
  exact fun g hg => hx ⟨g, hg⟩

theorem mulV_padic_smul (P : LocPrime l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (q : ℚ_[l]) (c : ↥(MaximalUnramifiedExtension l)) (x : V ⊗[ℚ_[l]] Bst P) :
    mulV P LL V (q • c) x = q • mulV P LL V c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [mulV_tmul, mulV_tmul, ← tmul_smul, Algebra.smul_def q c, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_assoc, ← Algebra.smul_def]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem mem_closure_mulV_of_finrank_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsPst P ρ → ∀ S : Submodule ↥LL.1 (V ⊗[ℚ_[l]] Bst P), S ≤ Dst P ρ → (∀ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 → ∀ x ∈ S, mulV P ↥LL.1 V c x ∈ S) → finrank ↥LL.1 ↥S = finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V → ∀ x ∈ Dpst P ρ, x ∈ AddSubgroup.closure {y | ∃ (c : ↥(MaximalUnramifiedExtension l)) (s : V ⊗[ℚ_[l]] Bst P), s ∈ S ∧ y = mulV P ↥LL.1 V c s} := by
  intro l _ P K LL V _ _ _ _ _ ρ hV S hS _ hrk x hx
  haveI := LL.2
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  obtain ⟨hfin, hd⟩ := (isPst_iff P ρ).mp hV
  let val : DpstUr P ρ →+ V ⊗[ℚ_[l]] Bst P :=
    (Dpst P ρ).subtype.toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom
  have hSD : S ≤ Dpst P ρ := fun s hs => (mem_Dpst P ρ).mpr ⟨K, fun g _ => (mem_Dst P ρ).mp (hS hs) g⟩
  obtain ⟨b, hbS, hsp, hli⟩ := exists_linearIndependent ↥(MaximalUnramifiedExtension l) {y : DpstUr P ρ | val y ∈ S}
  haveI : Finite ↥b := hli.finite
  letI : Fintype ↥b := Fintype.ofFinite _
  have hspan : ∀ y : DpstUr P ρ, y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) b → ∃ c : ↥b → ↥(MaximalUnramifiedExtension l),
      ∑ i, c i • (i : DpstUr P ρ) = y := fun y hy => by
    rw [← Submodule.mem_span_range_iff_exists_fun, Subtype.range_coe]; exact hy
  let inc : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)
  let f : (↥b → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    { toFun := fun c => ∑ i, mulV P ↥LL.1 V (inc (c i)) (val i)
      map_add' := fun c c' => by simp [Finset.sum_add_distrib]
      map_smul' := fun q c => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mulV_padic_smul P _ V q (inc (c i)) (val i) }
  have hle : S.restrictScalars ℚ_[l] ≤ LinearMap.range f := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨s, hSD hs⟩) (hsp ▸ Submodule.subset_span hs)
    have hfix : ∀ i, (c i : Om l) ∈ K.1 := fun i => mem_of_GK_fixed fun g => by
      have := semilinear_coord_fixed hli (fun a => ⟨_, galois_mem_Kur g a⟩)
        (actD P ρ g).toAddMonoidHom
        (fun a y => LinearMap.congr_fun (actD_mulD P ρ g a _ rfl) y)
        (fun j => Subtype.ext ((mem_Dst P ρ).mp (hS (hbS j.2)) g)) c
        (by rw [hc]; exact Subtype.ext ((mem_Dst P ρ).mp (hS hs) g)) i
      exact congrArg Subtype.val this
    refine ⟨fun i => ⟨c i, hfix i, (c i).2⟩, ?_⟩
    have := congrArg val hc
    rw [map_sum] at this
    exact this
  have h1 : finrank ℚ_[l] ↥(S.restrictScalars ℚ_[l]) ≤ Fintype.card ↥b * finrank ℚ_[l] ↥(K0 K) := by
    refine (Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le f).trans ?_)
    simp [Module.finrank_pi_fintype]
  have h2 : finrank ℚ_[l] ↥(S.restrictScalars ℚ_[l]) = finrank ℚ_[l] V * finrank ℚ_[l] ↥(K0 K) := by
    change finrank ℚ_[l] ↥S = _
    rw [← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 ↥S, hrk, ← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 V]
    ring
  have h3 : finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ Fintype.card ↥b := by
    rw [hd]
    exact Nat.le_of_mul_le_mul_right (h2 ▸ h1) Module.finrank_pos
  have htop := hli.span_eq_top_of_card_eq_finrank' (le_antisymm hli.fintype_card_le_finrank h3)
  rw [Subtype.range_coe] at htop
  obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨x, hx⟩) (htop ▸ Submodule.mem_top)
  have h4 := congrArg val hc
  rw [map_sum] at h4
  rw [← show _ = x from h4]
  exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨c i, val i, hbS i.2, rfl⟩

end GlobalTheory.Pst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemConjSmulOfAdjoint
section
open Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Pointwise Classical

namespace GlobalTheory.Mem.RowsBundle

theorem exists_conj_involution (I : AutInst) :
    ∃ cj : HeightOneSpectrum (𝓞 I.E) → HeightOneSpectrum (𝓞 I.E), (∀ v, cj (cj v) = v) ∧
      (∀ v v', IsConj I v v' ↔ v' = cj v) ∧
      ∀ (m : ℕ) (v : HeightOneSpectrum (𝓞 I.E)), (m : 𝓞 I.E) ∈ v.asIdeal → (m : 𝓞 I.E) ∈ (cj v).asIdeal := by
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hst2 : ∀ a, st (st a) = a := fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])
  have hsurj : Function.Surjective st := fun a => ⟨st a, hst2 a⟩
  let cj : HeightOneSpectrum (𝓞 I.E) → HeightOneSpectrum (𝓞 I.E) := fun v => v.comap st hsurj
  have hcj : ∀ v a, a ∈ (cj v).asIdeal ↔ st a ∈ v.asIdeal := fun v a => Iff.rfl
  refine ⟨cj, fun v => HeightOneSpectrum.ext (Ideal.ext fun a => by rw [hcj, hcj, hst2]), fun v v' => ?_,
    fun m v hv => by rw [hcj, map_natCast]; exact hv⟩
  constructor
  · intro h
    refine HeightOneSpectrum.ext (Ideal.ext fun b => ?_)
    rw [hcj]
    exact (h (st b) b (by rw [hst, star_star])).symm
  · rintro rfl a b hab
    have : b = st a := RingOfIntegers.ext hab
    subst this
    rw [hcj, hst2]

theorem meets_iff_card {X P : Type} (cj : X → X) (hc : ∀ v, cj (cj v) = v) (S : Set X) (hS : ∀ v ∈ S, cj v ∈ S)
    {m : ℕ} (hm : 0 < m) (hcard : S.ncard = 2 * m) (w : P → X) (hw : ∀ v, w v ∈ S) (hinj : Function.Injective w)
    (hn : ∀ v v', w v' ≠ cj (w v)) : (∀ u ∈ S, ∃ v, u = w v ∨ u = cj (w v)) ↔ Nat.card P = m := by
  let f : P ⊕ P → S := Sum.elim (fun v => ⟨w v, hw v⟩) (fun v => ⟨cj (w v), hS _ (hw v)⟩)
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) h
    · exact congrArg _ (hinj (congrArg Subtype.val h))
    · exact absurd (congrArg Subtype.val h) (hn _ _)
    · exact absurd (congrArg Subtype.val h).symm (hn _ _)
    · have h' : cj (w a) = cj (w b) := congrArg Subtype.val h
      exact congrArg _ (hinj (by rw [← hc (w a), h', hc]))
  have hS' : Nat.card S = 2 * m := hcard
  haveI : Finite S := Nat.finite_of_card_ne_zero (by omega)
  haveI : Finite P := Finite.of_injective _ (hf.comp Sum.inl_injective)
  have hP : Nat.card (P ⊕ P) = Nat.card P + Nat.card P := Nat.card_sum
  constructor
  · intro h
    have hs : Function.Surjective f := fun u => by
      obtain ⟨v, e | e⟩ := h u.1 u.2
      · exact ⟨Sum.inl v, Subtype.ext e.symm⟩
      · exact ⟨Sum.inr v, Subtype.ext e.symm⟩
    have := Nat.card_eq_of_bijective f ⟨hf, hs⟩
    omega
  · intro h u hu
    have hb := (Nat.bijective_iff_injective_and_card f).2 ⟨hf, by omega⟩
    obtain ⟨v | v, e⟩ := hb.2 ⟨u, hu⟩
    · exact ⟨v, Or.inl (congrArg Subtype.val e).symm⟩
    · exact ⟨v, Or.inr (congrArg Subtype.val e).symm⟩

theorem isChoice_of_card (I : AutInst) (g : Fin 2 → ℕ) (hg : ∀ k, (g k).Prime) (hne : g 0 ≠ g 1)
    (hsp : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal →
      Ideal.absNorm v.asIdeal = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ v.asIdeal ^ 2 ∧ ¬ IsConj I v v)
    {m : ℕ} (hm : 0 < m)
    (hcard : ∀ k, {v : HeightOneSpectrum (𝓞 I.E) | ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal}.ncard = 2 * m) :
    (∃ w : ∀ _ : Fin 2, Fin m → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin m) w) ∧
      ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)),
        (∀ k, Fintype.card (Pl k) = m) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) →
        (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
  obtain ⟨cj, hc, hconj, hmem⟩ := exists_conj_involution I
  obtain ⟨Pl₀, w₀, -, h₀⟩ := exists_choice I g hg hne hsp
  have key : ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)),
      (∀ k, Fintype.card (Pl k) = m) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) →
      (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
    intro Pl _ w h1 h2 h3 h4
    refine ⟨hg, hne, h₀.2.2.1, fun k v => ⟨h2 k v, (hsp k _ (h2 k v)).1⟩, h3, h4, fun k u hu => ?_⟩
    simp only [hconj] at h4 ⊢
    exact (meets_iff_card cj hc _ (hmem (g k)) hm (hcard k) (w k) (h2 k) (h3 k) (h4 k)).2
      (by rw [Nat.card_eq_fintype_card, h1]) u hu
  refine ⟨?_, key⟩
  obtain ⟨-, -, -, h2, h3, h4, h5⟩ := h₀
  have hP : ∀ k, Nat.card (Pl₀ k) = m := fun k => by
    simp only [hconj] at h4 h5
    exact (meets_iff_card cj hc _ (hmem (g k)) hm (hcard k) (w₀ k) (fun v => (h2 k v).1) (h3 k) (h4 k)).1 (h5 k)
  have e : ∀ k, Fin m ≃ Pl₀ k := fun k =>
    haveI : Finite (Pl₀ k) := Nat.finite_of_card_ne_zero (by rw [hP]; omega)
    (Finite.equivFinOfCardEq (hP k)).symm
  exact ⟨fun k v => w₀ k (e k v), key _ _ (fun _ => Fintype.card_fin m) (fun k v => (h2 k _).1)
    (fun k => (h3 k).comp (e k).injective) fun k v v' => h4 k _ _⟩

section Unip

variable {I : AutInst}

theorem hAf_eq_dot (u v : Fin I.n → I.E ⊗[I.F] Af I.F) : hAf I u v =
    (fun i => sigR I.cm.sig (Af I.F) (u i)) ⬝ᵥ (I.J.map (inclE (F := I.F) (Af I.F)) *ᵥ v) := by
  simp only [hAf, hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hAf_inv_mulVec (x : I.Gf) (y z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I (I.fmat x⁻¹ *ᵥ y) z = hAf I y (I.fmat x *ᵥ z) := by
  have hx : cT (sigR I.cm.sig (Af I.F)) (I.fmat x⁻¹) * I.J.map (inclE (F := I.F) (Af I.F)) * I.fmat x⁻¹ = _ := x⁻¹.2
  have hs : (fun i => sigR I.cm.sig (Af I.F) ((I.fmat x⁻¹ *ᵥ y) i)) =
      (fun i => sigR I.cm.sig (Af I.F) (y i)) ᵥ* cT (sigR I.cm.sig (Af I.F)) (I.fmat x⁻¹) := by
    funext i
    simp [Matrix.mulVec, Matrix.vecMul, dotProduct, cT, map_sum, mul_comm]
  have h1 : I.fmat x⁻¹ * I.fmat x = 1 := by rw [← fmat_mul, inv_mul_cancel, fmat_one]
  rw [hAf_eq_dot, hAf_eq_dot, hs, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  conv_rhs => rw [← hx, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem hAf_pow_adjoint (x : I.Gf) (m : ℕ) (y z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I ((I.fmat x⁻¹ - 1) ^ m *ᵥ y) z = hAf I y ((I.fmat x - 1) ^ m *ᵥ z) := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← ih, Matrix.sub_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]
    generalize (I.fmat x⁻¹ - 1) ^ m *ᵥ y = u
    have h := hAf_inv_mulVec x u z
    simp only [hAf, hform, Pi.sub_apply, map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib] at h ⊢
    rw [h]

theorem sub_one_pow_mem {x : I.Gf} (hx : x ∈ I.Kset) (m : ℕ) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    (I.fmat x - 1) ^ m *ᵥ y ∈ I.Lf := by
  induction m with
  | zero => simpa using hy
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (mulVec_mem hx ih) ih

end Unip

end GlobalTheory.Mem.RowsBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemilinearBasisImageIndepOfBasis
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

theorem semilinear_basis_image_indep_of_basis :
    ∀ (K : Type) [Field K] (e : K →+* ℂ) (V : Type) [AddCommGroup V] [Module K V]
      (W : Type) [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[e] W) (ι κ : Type)
      (b : Module.Basis ι K V) (b' : Module.Basis κ K V),
      (LinearIndependent ℂ (fun i => j (b i)) ∧
        Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) →
      LinearIndependent ℂ (fun i => j (b' i)) ∧
        Submodule.span ℂ (Set.range fun i => j (b' i)) = ⊤ := by
  intro K _ e V _ _ W _ _ j ι κ b b' ⟨hli, hsp⟩
  letI : Algebra K ℂ := e.toAlgebra
  letI : Module K W := Module.compHom W e
  haveI : IsScalarTower K ℂ W := ⟨fun k c w => by
    change (e k * c) • w = e k • c • w
    exact mul_smul _ _ _⟩
  let j' : V →ₗ[K] W :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun k v => j.map_smulₛₗ k v }
  let L : ℂ ⊗[K] V →ₗ[ℂ] W := j'.liftBaseChange ℂ
  have hL : ∀ v : V, L (1 ⊗ₜ[K] v) = j v := fun v => by
    simp [L, j']
  let c : Module.Basis ι ℂ W := Module.Basis.mk hli hsp.ge
  let E : ℂ ⊗[K] V ≃ₗ[ℂ] W := (b.baseChange ℂ).equiv c (Equiv.refl ι)
  have hE : (E : ℂ ⊗[K] V →ₗ[ℂ] W) = L := by
    refine (b.baseChange ℂ).ext fun i => ?_
    rw [LinearEquiv.coe_coe]
    simp only [E, Module.Basis.equiv_apply, Equiv.refl_apply, c, Module.Basis.mk_apply]
    rw [Module.Basis.baseChange_apply, hL]
  have hb : (fun i => j (b' i)) = ⇑((b'.baseChange ℂ).map E) := by
    funext i
    rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, ← hL, ← hE, LinearEquiv.coe_coe]
  rw [hb]
  exact ⟨Module.Basis.linearIndependent _, Module.Basis.span_eq _⟩

end GlobalTheory
end

