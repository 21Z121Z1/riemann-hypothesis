import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0227
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelExistsAfterBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.LevelRaise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem exists_enum (o : Obj D l b s) {M : ℕ} (hM : 0 < M) :
    ∃ (J : Type) (_ : Finite J), ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
      ∃ u : J → (Over.mk x ⟶ o.t.G), Function.Injective u ∧ ∀ w, w ^ M = 1 ↔ ∃ j, u j = w := by
  obtain ⟨J, _, π, r, hr, hπ⟩ := LevelFlat.exists_finite_quotient D M hM
  refine ⟨J, inferInstance, fun K _ _ x => ?_⟩
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨-, I, -⟩ := o.geom K x β.hom hβ.symm
  have hI : ∀ a b, I.ev M a = I.ev M b ↔ π a = π b := fun a b => by
    have h : I.ev M a = I.ev M (a - b) * I.ev M b := by rw [← I.add, sub_add_cancel]
    rw [hπ, h, mul_eq_right, I.ker M hM]
    rfl
  refine ⟨fun j => I.ev M (r j), fun i j hij => ?_, fun w => (I.onto M hM w).trans ⟨?_, ?_⟩⟩
  · have := (hI _ _).1 hij
    rwa [hr, hr] at this
  · rintro ⟨a, rfl⟩
    exact ⟨π a, (hI _ _).2 (hr _)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, rfl⟩

theorem exists_eq_comp (o : Obj D l b s) {M : ℕ} (hM : 0 < M) {K L : Type} [Field K] [Field L]
    [IsAlgClosed K] [IsAlgClosed L] {x : Sp K ⟶ S} {y : Sp L ⟶ S} (ψ : K →+* L) (g : Over.mk y ⟶ Over.mk x)
    (hg : g.left = spMap ψ) (w : Over.mk y ⟶ o.t.G) (hw : w ^ M = 1) :
    ∃ a : Over.mk x ⟶ o.t.G, a ^ M = 1 ∧ g ≫ a = w := by
  obtain ⟨J, _, hJ⟩ := exists_enum o hM
  obtain ⟨u, hu, hu'⟩ := hJ K x
  obtain ⟨v, -, hv'⟩ := hJ L y
  have hp : ∀ j, u j ^ M = 1 := fun j => (hu' _).2 ⟨j, rfl⟩
  choose τ hτ using fun j => (hv' (g ≫ u j)).1 (by rw [← MonObj.comp_pow, hp, MonObj.comp_one])
  have hτi : Function.Injective τ := fun i j hij =>
    hu (TorsionRat.comp_injective ψ g hg (by rw [← hτ, ← hτ, hij]))
  obtain ⟨j, rfl⟩ := (hv' w).1 hw
  obtain ⟨i, rfl⟩ := Finite.surjective_of_injective hτi j
  exact ⟨u i, hp i, (hτ i).symm⟩

theorem exists_finite_set (o : Obj D l b s) {M : ℕ} (hM : 0 < M) {K F : Type} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed F] (x : Sp K ⟶ S) :
    ∃ T : Set F, T.Finite ∧ ∀ L : IntermediateField K F, T ⊆ L →
      ∀ w : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ o.t.G, w ^ M = 1 →
        ∃ q : Over.mk (spMap (algebraMap K L) ≫ x) ⟶ o.t.G, spMap (algebraMap L F) ≫ q.left = w.left := by
  haveI := o.proper
  obtain ⟨J, _, hJ⟩ := exists_enum o hM
  obtain ⟨u, -, hu⟩ := hJ F (spMap (algebraMap K F) ≫ x)
  choose T hT using fun j => TorsionRat.exists_finset_over o.t.G x (u j)
  refine ⟨⋃ j, (T j : Set F), Set.finite_iUnion fun j => (T j).finite_toSet, fun L hL w hw => ?_⟩
  obtain ⟨j, rfl⟩ := (hu w).1 hw
  exact hT j L ((Set.subset_iUnion (fun j => (T j : Set F)) j).trans hL)

theorem exists_field {k : Type} [Field k] [NumberField k] {s : Sp k ⟶ Sp B} (o : Obj D l b s) {M : ℕ} (hM : 0 < M)
    (σ : k →+* ℂ) (C : IntermediateField ℚ ℂ) [FiniteDimensional ℚ C] :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (i : k →+* L) (j : C →+* L) (σ' : L →+* ℂ),
      σ'.comp i = σ ∧ (∀ c, σ' (j c) = c) ∧
      ∀ w : Over.mk (spMap σ' ≫ spMap i) ⟶ o.t.G, w ^ M = 1 →
        ∃ q : Sp L ⟶ o.t.G.left, q ≫ o.t.G.hom = spMap i ∧ spMap σ' ≫ q = w.left := by
  letI : Algebra k ℂ := σ.toAlgebra
  let F := algebraicClosure k ℂ
  haveI : IsAlgClosed F := (algebraicClosure.isAlgClosure k ℂ).isAlgClosed
  have hC : ∀ c : C, (c : ℂ) ∈ F := fun c => by
    rw [mem_algebraicClosure_iff]
    have h1 : IsAlgebraic ℚ (c : ℂ) :=
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c).algHom C.val
    exact h1.tower_top k
  let g : C →+* F := (C.val : C →+* ℂ).codRestrict F hC
  obtain ⟨T, hT, hT'⟩ := exists_finite_set o hM (K := k) (F := F) (𝟙 _)
  obtain ⟨U, hU⟩ := (Module.Finite.fg_top (R := ℚ) (M := C))
  let T' : Set F := T ∪ g '' U
  haveI : Finite T' := (hT.union (U.finite_toSet.image g)).to_subtype
  let L := IntermediateField.adjoin k T'
  haveI : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hg : ∀ c, g c ∈ L := fun c => by
    have hc : c ∈ Submodule.span ℚ (U : Set C) := hU ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ (Or.inr ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul q x _ hx =>
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact mul_mem (SubfieldClass.ratCast_mem L q) hx
  refine ⟨L, inferInstance, NumberField.of_module_finite k L, algebraMap k L, g.codRestrict L hg,
    (algebraMap F ℂ).comp (algebraMap L F), rfl, fun c => rfl, fun w hw => ?_⟩
  let g₂ : Over.mk (spMap ((algebraMap F ℂ).comp (algebraMap L F)) ≫ spMap (algebraMap k L)) ⟶
      Over.mk (spMap (algebraMap k F) ≫ 𝟙 _) := Over.homMk (spMap (algebraMap F ℂ)) (by
    change spMap (algebraMap F ℂ) ≫ spMap (algebraMap k F) ≫ 𝟙 _ =
      spMap ((algebraMap F ℂ).comp (algebraMap L F)) ≫ spMap (algebraMap k L)
    rw [Category.comp_id, TorsionRat.sp_comp, TorsionRat.sp_comp]
    rfl)
  obtain ⟨a, ha, ha'⟩ := exists_eq_comp o hM (algebraMap F ℂ) g₂ rfl w hw
  obtain ⟨q, hq⟩ := hT' L (Set.subset_union_left.trans (IntermediateField.subset_adjoin _ _)) a ha
  refine ⟨q.left, (Over.w q).trans (Category.comp_id _), ?_⟩
  have h1 : spMap (algebraMap F ℂ) ≫ a.left = w.left := congrArg CommaMorphism.left ha'
  rw [← h1, ← hq, ← TorsionRat.sp_comp, Category.assoc]

theorem exists_obj_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (c₂ : Coeff l₂) (k : Type) [Field k] [NumberField k] (s : Sp k ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s), 1 ≤ D.p + D.q → l₂.A = 1 → ∃ (k' : Type) (_ : Field k') (_ : NumberField k') (i : k →+* k') (j₂ : c₂.F →+* k') (o₂ : Obj D l₂ (baseKA l₂) (spMap j₂ ≫ spMap (IntermediateField.inclusion c₂.le).toRingHom)), Nonempty (SABMap o₂.t o.t (spMap i)) := by
  intro E _ _ _ H D l l₂ c₂ k _ _ s o _ hA
  obtain ⟨b₀, rfl⟩ : ∃ ν : KA l →+* k, s = spMap ν := ⟨(Spec.preimage s).hom, (Spec.map_preimage s).symm⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : k →+* ℂ, ∀ a, σ (b₀ a) = a := by
    letI : Algebra (KA l) k := b₀.toAlgebra
    haveI : Algebra.IsAlgebraic (KA l) k := Algebra.IsAlgebraic.tower_top (K := ℚ) (KA l)
    let τ : k →ₐ[KA l] ℂ := IsAlgClosed.lift
    exact ⟨τ, fun a => τ.commutes a⟩
  have hM : 0 < l₂.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l₂.three_le) l₂.A_pos
  haveI := c₂.fin
  obtain ⟨L, _, _, i, j, σ', hi, hj, hrat⟩ := exists_field o hM σ c₂.F
  obtain ⟨t', ⟨m⟩⟩ := exists_sab (spMap i) o.t
  let o' := ModelCompare.objOfSABMap o m
  let T : PAT H (Sp L) := ⟨t', ObjDim.isAbelianScheme o', _, ObjDim.smoothOfRelativeDimension o', ObjDim.sym,
    o'.ample, o'.ktriv⟩
  let j' : KA l₂ →+* L := j.comp (IntermediateField.inclusion c₂.le).toRingHom
  have hρ : j' (baseKA l₂).ρ = i (b₀ (baseKA l).ρ) := σ'.injective (by
    rw [← RingHom.comp_apply σ' i, hi, hσ]
    exact hj _)
  have hs : ∀ {k₁ : Type} [Field k₁] (β : L →+* k₁),
      spMap β ≫ spMap i ≫ spMap b₀ = spMap (β.comp (i.comp b₀)) := fun β => by
    rw [TorsionRat.sp_comp, TorsionRat.sp_comp]
  obtain ⟨-, I, -⟩ := o'.geom ℂ (spMap σ') _ (hs σ')
  obtain ⟨o₂, ho₂⟩ := RationalTorsion.exists_obj abelianSchemeLaws_all.1 E H D l₂ (KA l₂) (baseKA l₂) L j' σ' T I
    (fun k₁ _ _ β _ => by
      rw [hρ]
      exact (o'.geom k₁ (spMap β) _ (hs β)).1)
    (by
      have h1 := I.ζ_prim 1 one_pos
      have h2 := (baseKA l₂).ζ_prim
      rw [hA] at h2 ⊢
      rw [IsPrimitiveRoot.one_right_iff] at h1 h2
      rw [h1, h2, map_one, map_one, Units.val_one])
    (fun x hx => by
      obtain ⟨q, hq, hq'⟩ := hrat (ObjPull.pushEquiv m.cart (Over.mk (spMap σ')) x) (by rw [← map_pow, hx, map_one])
      refine ⟨Over.homMk (m.cart.1.lift q (𝟙 _) (hq.trans (Category.id_comp _).symm)) (m.cart.1.lift_snd _ _ _), ?_⟩
      apply Over.OverMorphism.ext
      apply m.cart.1.hom_ext
      · rw [Over.comp_left, ObjPull.toUnit_left', Category.assoc]
        exact (congrArg (spMap σ' ≫ ·) (m.cart.1.lift_fst _ _ _)).trans hq'
      · rw [Over.w, Over.w])
  refine ⟨L, inferInstance, inferInstance, i, j, ?_⟩
  rw [TorsionRat.sp_comp]
  exact ⟨o₂, ho₂ ▸ ⟨m⟩⟩

end GlobalTheory.LevelRaise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateEisensteinHolomorphicDerivative
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.CircleDop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem exp_smul_add {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • Z) = NormedSpace.exp (s • Z) * NormedSpace.exp (t • Z) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Z).smul_left s).smul_right t)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem continuous_exp_smul {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • Z) :=
  NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

theorem realLine_hom (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    (∀ s t, γ (s + t) = γ s * γ t) ∧ Continuous γ := by
  obtain ⟨w, τ, Z, -, hy⟩ := hγ
  choose y hy1 hy2 using hy
  have inj : ∀ a b : GArch σ J w, GlobalTheory.Orb.archMat σ J τ a = GlobalTheory.Orb.archMat σ J τ b → a = b := fun a b e => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at e
    exact (archEquiv J h τ).injective (Subtype.ext (Units.ext e))
  have hyadd : ∀ s t, y (s + t) = y s * y t := fun s t =>
    inj _ _ (by rw [map_mul, hy2, hy2, hy2, exp_smul_add])
  refine ⟨fun s t => by rw [hy1, hy1, hy1, hyadd, map_mul], ?_⟩
  have hyc : Continuous y := (GlobalTheory.Orb.isEmbedding_archMat _ h τ).continuous_iff.2 (by
    change Continuous fun t => fun i j => GlobalTheory.Orb.archMat σ J τ (y t) i j
    simp only [hy2]
    exact continuous_pi fun i => continuous_pi fun j => (continuous_exp_smul Z).matrix_elem i j)
  rw [show γ = fun t => embArch σ J w (y t) from funext hy1]
  exact (continuous_embArch σ J w).comp hyc

theorem hasDerivAt_line {f : GAd σ J → ℂ} (hf : GlobalTheory.WeakHolFamily.SmoothLines σ J f) {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) (hadd : ∀ s t, γ (s + t) = γ s * γ t) (g : GAd σ J) (t : ℝ) :
    HasDerivAt (fun u => f (g * γ u)) (lineDer γ f (g * γ t)) t := by
  have h0 : HasDerivAt (fun u => f (g * γ t * γ u)) (lineDer γ f (g * γ t)) (t - t) := by
    rw [sub_self]; exact (GlobalTheory.WeakHolFamily.differentiable_line hf hγ (g * γ t) 0).hasDerivAt
  have h1 := HasDerivAt.comp_sub_const t t h0
  have e : (fun u => f (g * γ u)) = fun x => f (g * γ t * γ (x - t)) := funext fun u => by
    rw [mul_assoc, ← hadd, add_sub_cancel]
  rw [e]
  exact h1

theorem lineDer_circleIntegral (h : IsCMExt F E σ) {K : ℂ → GAd σ J → ℂ} {c : ℂ → ℂ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn c (Metric.sphere s₀ r))
    (hK : ∀ w ∈ Metric.sphere s₀ r, GlobalTheory.WeakHolFamily.SmoothLines σ J (K w))
    {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ)
    (hcont : ∀ g, ContinuousOn (fun w => K w g) (Metric.sphere s₀ r))
    (hcont' : ∀ g, ContinuousOn (fun w => lineDer γ (K w) g) (Metric.sphere s₀ r))
    (hbd : ∃ (N : ℕ) (C : ℝ), ∀ w ∈ Metric.sphere s₀ r, ∀ g, ‖lineDer γ (K w) g‖ ≤ C * (height σ J g : ℝ) ^ N)
    (g : GAd σ J) :
    lineDer γ (fun g => ∮ w in C(s₀, r), c w * K w g) g = ∮ w in C(s₀, r), c w * lineDer γ (K w) g := by
  obtain ⟨hadd, hγc⟩ := realLine_hom h hγ
  obtain ⟨N, C, hC⟩ := hbd
  have hγ0 : γ 0 = 1 := by
    have := hadd 0 0; rw [add_zero] at this; exact mul_eq_left.1 this.symm
  have hmem : ∀ θ, circleMap s₀ r θ ∈ Metric.sphere s₀ r := fun θ => circleMap_mem_sphere s₀ hr.le θ
  obtain ⟨Mc, hMc⟩ := (isCompact_sphere s₀ r).exists_bound_of_continuousOn hc
  have hMc0 : 0 ≤ Mc := (norm_nonneg _).trans (hMc _ (hmem 0))
  have hht : Continuous fun t => (height σ J (γ t) : ℝ) :=
    NNReal.continuous_coe.comp ((continuous_height_GAd σ J).comp hγc)
  obtain ⟨Hγ, hHγ⟩ := (isCompact_closedBall (0 : ℝ) 1).exists_bound_of_continuousOn hht.continuousOn
  set Y : ℝ := (height σ J g : ℝ) * |Hγ| with hY
  have hdc : Continuous fun θ => deriv (circleMap s₀ r) θ := by
    rw [show (fun θ => deriv (circleMap s₀ r) θ) = fun θ => circleMap 0 r θ * Complex.I from
      funext fun θ => deriv_circleMap s₀ r θ]
    exact (continuous_circleMap 0 r).mul continuous_const
  have hnd : ∀ θ, ‖deriv (circleMap s₀ r) θ‖ = |r| := fun θ => by
    rw [deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
  let Fn : ℝ → ℝ → ℂ := fun t θ => deriv (circleMap s₀ r) θ • (c (circleMap s₀ r θ) * K (circleMap s₀ r θ) (g * γ t))
  let Fn' : ℝ → ℝ → ℂ := fun t θ =>
    deriv (circleMap s₀ r) θ • (c (circleMap s₀ r θ) * lineDer γ (K (circleMap s₀ r θ)) (g * γ t))
  have hcc : Continuous fun θ => c (circleMap s₀ r θ) := hc.comp_continuous (continuous_circleMap s₀ r) hmem
  have hFc : ∀ t, Continuous (Fn t) := fun t =>
    hdc.smul (hcc.mul ((hcont (g * γ t)).comp_continuous (continuous_circleMap s₀ r) hmem))
  have hFc' : ∀ t, Continuous (Fn' t) := fun t =>
    hdc.smul (hcc.mul ((hcont' (g * γ t)).comp_continuous (continuous_circleMap s₀ r) hmem))
  have hL : ∀ w ∈ Metric.sphere s₀ r, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖lineDer γ (K w) (g * γ t)‖ ≤ |C| * Y ^ N := by
    intro w hw t ht
    have h1 : (height σ J (g * γ t) : ℝ) ≤ Y := by
      have e1 : (height σ J (g * γ t) : ℝ) ≤ (height σ J g : ℝ) * (height σ J (γ t) : ℝ) := by
        exact_mod_cast height_mul_le σ J g (γ t)
      have e2 : (height σ J (γ t) : ℝ) ≤ |Hγ| := by
        have := hHγ t (Metric.ball_subset_closedBall ht)
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans (this.trans (le_abs_self _))
      exact e1.trans (mul_le_mul_of_nonneg_left e2 (NNReal.coe_nonneg _))
    refine (hC w hw _).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (NNReal.coe_nonneg _) N)).trans ?_)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) h1 N) (abs_nonneg C)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := 0) (b := 2 * Real.pi)
    (F := Fn) (F' := Fn') (x₀ := (0 : ℝ)) (bound := fun _ => |r| * (Mc * (|C| * Y ^ N)))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) (Filter.Eventually.of_forall fun t => (hFc t).aestronglyMeasurable)
    ((hFc 0).intervalIntegrable _ _) (hFc' 0).aestronglyMeasurable
    (ae_of_all _ fun θ _ t ht => by
      simp only [Fn', norm_smul, norm_mul, hnd]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hMc _ (hmem θ)) (hL _ (hmem θ) t ht) (norm_nonneg _) hMc0)
        (abs_nonneg r))
    intervalIntegrable_const
    (ae_of_all _ fun θ _ t _ =>
      ((hasDerivAt_line (hK _ (hmem θ)) hγ hadd g t).const_mul (c (circleMap s₀ r θ))).const_smul
        (deriv (circleMap s₀ r) θ))
  show deriv (fun t => ∫ θ in (0 : ℝ)..2 * Real.pi, Fn t θ) 0 = _
  rw [key.2.deriv]
  simp only [Fn', hγ0, mul_one]
  rfl

end GlobalTheory.CircleDop

namespace GlobalTheory.CircleDop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem foldr_circleIntegral (h : IsCMExt F E σ) (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ)
    (hV : IsOpen V) (hr : 0 < r) (hsub : Metric.closedBall s₀ r ⊆ V) (hH : ∀ s ∈ V, IsSmoothModerate σ J (H₀ s))
    (hμ : ∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) (j : ℤ) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∀ g,
      l.foldr lineDer (fun g => ∮ w in C(s₀, r), (w - s₀) ^ j * H₀ w g) g =
        ∮ w in C(s₀, r), (w - s₀) ^ j * l.foldr lineDer (H₀ w) g
  | [], _, _ => rfl
  | γ :: l, hl, g => by
    have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h' => hl γ' (List.mem_cons_of_mem _ h')
    have hγ := hl γ List.mem_cons_self
    have ih := foldr_circleIntegral h H₀ s₀ r V hV hr hsub hH hμ j l hl'
    have hS : Metric.sphere s₀ r ⊆ V := Metric.sphere_subset_closedBall.trans hsub
    have W1 := GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ V (Metric.sphere s₀ r) hV
      (isCompact_sphere s₀ r) hS hH hμ l hl'
    have W2 := GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ V (Metric.sphere s₀ r) hV
      (isCompact_sphere s₀ r) hS hH hμ (γ :: l) hl
    obtain ⟨N, C, hC⟩ := W2.2
    rw [List.foldr_cons, show l.foldr lineDer (fun g => ∮ w in C(s₀, r), (w - s₀) ^ j * H₀ w g) =
      fun g => ∮ w in C(s₀, r), (w - s₀) ^ j * l.foldr lineDer (H₀ w) g from funext ih]
    refine lineDer_circleIntegral h hr ?_ (fun w hw => GlobalTheory.WeakHolFamily.smoothLines_foldr (hH w (hS hw)).smooth l hl')
      hγ (fun g => (W1.1 g).continuousOn.mono hS) (fun g => (W2.1 g).continuousOn.mono hS) ⟨N, C, hC⟩ g
    exact (continuousOn_id.sub continuousOn_const).zpow₀ j fun w hw =>
      Or.inl (sub_ne_zero.2 (Metric.ne_of_mem_sphere hw hr.ne'))

theorem dop_circleIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ),
    IsOpen V → 0 < r → Metric.closedBall s₀ r ⊆ V → (∀ s ∈ V, IsSmoothModerate σ J (H₀ s)) →
    (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) → ∀ j : ℤ,
    ∀ z : List (ℝ → GAd σ J) →₀ ℂ, (∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) → ∀ g,
      GlobalTheory.UAut.dop z (fun g => circleIntegral (fun w => (w - s₀) ^ j * H₀ w g) s₀ r) g =
        circleIntegral (fun w => (w - s₀) ^ j * GlobalTheory.UAut.dop z (H₀ w) g) s₀ r := by
  intro F E _ _ _ _ _ σ h n J _ H₀ s₀ r V hV hr hsub hH hμ j z hz g
  have hS : Metric.sphere s₀ r ⊆ V := Metric.sphere_subset_closedBall.trans hsub
  have hc : ContinuousOn (fun w : ℂ => (w - s₀) ^ j) (Metric.sphere s₀ r) :=
    (continuousOn_id.sub continuousOn_const).zpow₀ j fun w hw =>
      Or.inl (sub_ne_zero.2 (Metric.ne_of_mem_sphere hw hr.ne'))
  have hint : ∀ l ∈ z.support,
      CircleIntegrable (fun w => z l * ((w - s₀) ^ j * l.foldr lineDer (H₀ w) g)) s₀ r := fun l hl =>
    ContinuousOn.circleIntegrable hr.le (continuousOn_const.mul (hc.mul
      (((GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ V (Metric.sphere s₀ r) hV
        (isCompact_sphere s₀ r) hS hH hμ l (hz l hl)).1 g).continuousOn.mono hS)))
  simp only [GlobalTheory.UAut.dop, Finsupp.sum]
  rw [show (fun w => (w - s₀) ^ j * ∑ l ∈ z.support, z l * l.foldr lineDer (H₀ w) g) =
      fun w => ∑ l ∈ z.support, z l * ((w - s₀) ^ j * l.foldr lineDer (H₀ w) g) from
    funext fun w => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
  rw [circleIntegral.integral_fun_sum hint]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [circleIntegral.integral_const_mul, foldr_circleIntegral h H₀ s₀ r V hV hr hsub hH hμ j l (hz l hl) g]

end GlobalTheory.CircleDop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
section
noncomputable section

namespace GlobalTheory.ThKAdm

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

variable (σ W) in

def FinPt : Set (UA σ W.J) := {g | At (fun a : AF F => a.2) (mat g - 1)}

variable (W) in

def IsLevel (L : Subgroup (UA σ W.J)) : Prop :=
  (L : Set (UA σ W.J)) ⊆ FinPt σ W ∧ ∃ U : Set (UA σ W.J), IsOpen U ∧ (1 : UA σ W.J) ∈ U ∧ U ∩ FinPt σ W ⊆ L

def IsKRep (B : Base F E) {m : ℕ} (τ : UA σ W.J → (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))) : Prop :=
  τ 1 = 1 ∧ (∀ k ∈ KInf σ W B.emb, ∀ k' ∈ KInf σ W B.emb, τ (k * k') = τ k * τ k') ∧
    (∀ k ∈ KInf σ W B.emb, ∀ v, ‖τ k v‖ = ‖v‖) ∧ ∀ v, ContinuousOn (fun k => τ k v) (KInf σ W B.emb)

def HasTypes (B : Base F E) (om : Rep σ Y W) {m : ℕ}
    (τ : UA σ W.J → (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))) (Ψ : Fn F n d) : Prop :=
  ∃ T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] Fn F n d, (∀ k ∈ KInf σ W B.emb, ∀ v, T (τ k v) = om (1, k) (T v)) ∧
    Ψ ∈ LinearMap.range T

end GlobalTheory.ThKAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorFamilyAdjointLiftSingleEigensystem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.UpSystem

theorem flatMap_cast (l : List ℕ) : List.flatMap (fun a : ℕ => [(a : ℤ)]) l = List.map (fun a : ℕ => (a : ℤ)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem labIn_eq (n : ℕ) (s : List ℕ) : Formalism.IndefR.Links.labIn n s =
    List.map (fun a : ℕ => (a : ℤ)) s ++ List.replicate (n - 2 * s.length) 0 ++ List.map (fun a : ℕ => -(a : ℤ)) s.reverse := by
  unfold Formalism.IndefR.Links.labIn
  simp only [List.bind_eq_flatMap, List.pure_def, flatMap_cast, List.map_map]
  rfl

theorem labIn_pairwise {n : ℕ} {s : List ℕ} (h : Formalism.L2.Col.InertTypeOk n s) :
    (Formalism.IndefR.Links.labIn n s).Pairwise (fun a b : ℤ => b ≤ a) := by
  obtain ⟨h1, -, -⟩ := h
  rw [labIn_eq]
  refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact List.pairwise_map.2 (h1.imp fun h => by exact_mod_cast h)
  · exact List.pairwise_replicate.2 (Or.inr le_rfl)
  · intro a ha b hb
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    rw [List.eq_of_mem_replicate hb]
    exact Int.natCast_nonneg x
  · rw [List.pairwise_map, List.pairwise_reverse]
    exact h1.imp fun h => by omega
  · intro a ha b hb
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 ha
      omega
    · rw [List.eq_of_mem_replicate ha]
      omega

end GlobalTheory.UpSystem

namespace GlobalTheory.UpSystem

set_option maxHeartbeats 1000000 in

theorem up_sys : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∃ Tc : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H, (∀ i f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = Tc i (R.jX A3.A.μ0 f)) ∧ ∀ c, ∃ x : (A3.rowI A3.A.μ0).OpIx → ℂ, ∀ w ∈ R.EEc c, ∀ i, Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = x i • LinearMap.adjoint (R.Th A3.A.μ0) w := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hI hOk hW hEx hS hTS hInert
  have h1 := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hW
  have hC := h1.1 hEx
  have hSF := h1.2.1
  have hIn := h1.2.2.1
  have hEE := h1.2.2.2.2.1
  choose hX hXo _ using (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0
  have hf := GlobalTheory.AdjBlock.model_form (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ)
    (J := (levEnv _ R.βX (R.datXt A3.A.μ0)).J) (χ := (levEnv _ R.βX (R.datXt A3.A.μ0)).χ) (R.B.R A3.A.μ0).pres
    (R.HX A3.A.μ0) (hC.models.HX A3.A.μ0) (hC.models.jX A3.A.μ0)
  choose Tc hTc using fun i => GlobalTheory.AdjBlock.exists_cx hf.1 hf.2.1 ((A3.rowI A3.A.μ0).opAll i)
  refine ⟨Tc, fun i f => (hTc i f).symm, fun c => ?_⟩
  have hext : ∀ i (U : Module.End ℂ (R.HX A3.A.μ0).H),
      (∀ f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = U (R.jX A3.A.μ0 f)) → Tc i = U :=
    fun i U hU => GlobalTheory.AdjBlock.ext_of_span hf.2.1 fun f => (hTc i f).trans (hU f)
  have hzero : ∀ i, (A3.rowI A3.A.μ0).opAll i = 0 → Tc i = 0 := by
    intro i h0
    refine hext i 0 (fun f => ?_)
    have e1 : (A3.rowI A3.A.μ0).opAll i f = 0 := by rw [h0]; rfl
    exact (congrArg (R.jX A3.A.μ0) e1).trans ((map_zero _).trans (LinearMap.zero_apply _).symm)
  have hsys : ∀ P, Good R.toRealDat A3.A.μ0 P → ∀ cX c0, GlobalTheory.Hk3.MatchE R.toRealDat A3.A.μ0 P cX c0 → ∀ i,
      Tc i = hX P cX → ∃ a : ℂ, ∀ w ∈ R.EEc c,
        Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    intro P hP cX c0 hm i hi
    have h10 := (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 hC hS R.SF hSF A3.A.μ0 P hP cX c0 hm hX hXo).2 c
    refine ⟨_, fun w hw => (congrArg (fun U : Module.End ℂ (R.HX A3.A.μ0).H => U (LinearMap.adjoint (R.Th A3.A.μ0) w)) hi).trans
      (h10 w ((hEE c).symm ▸ hw))⟩
  have hev0 : ∀ i, Tc i = 0 → ∃ a : ℂ, ∀ w ∈ R.EEc c,
      Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := fun i h0 =>
    ⟨0, fun w _ => (congrArg (fun U : Module.End ℂ (R.HX A3.A.μ0).H => U (LinearMap.adjoint (R.Th A3.A.μ0) w)) h0).trans
      ((LinearMap.zero_apply _).trans (zero_smul ℂ _).symm)⟩
  have key : ∀ i, ∃ a : ℂ, ∀ w ∈ R.EEc c,
      Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    rintro (⟨P, k⟩ | ⟨Q, y⟩)
    · by_cases hk : k ≤ D.sp.X'.rank
      · have hgood := ((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev).2.2.2 hC.fam A3.A.μ0 P.1 P.2).1
        have h99 := GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift R.toRealDat F.lv2 hI hC hS A3.A.μ0 (P : A3.A.ok A3.A.μ0)
        have hso := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0 hX hXo
          (P : A3.A.ok A3.A.μ0) k hk
        exact hsys _ hgood _ _ (h99.choose_spec.1 k hk) _ (hext _ _ hso)
      · exact hev0 _ (hzero _ ((hC.fam.degR A3.A.μ0 P).2 k (not_le.1 hk)))
    · refine Or.elim (hInert.1 A3.A.μ0 ((Q : A3.okI A3.A.μ0), y)) (fun h0 => ?_) (fun hy => ?_)
      · exact hev0 (Sum.inr (Q, y)) (hzero (Sum.inr (Q, y)) h0)
      · have hgc := hIn A3.A.μ0 Q.1 Q.2
        have tie := (hW.inert.hR A3.A.μ0).some
        have hy'' : Formalism.L2.Col.InertTypeOk D.sp.X'.rank hy.choose := R.B.rankR ▸ hy.choose_spec.1
        have h78 := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hC.lev hC.fam hC.models A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
          (fun i => R.plI i.1) (fun i => Formalism.IndefR.Links.labIn D.sp.X'.rank i.2) (A3.heckeRI A3.A.μ0)
          (fun i => Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2)
          (fun i hi => ⟨(hIn A3.A.μ0 i.1.1 i.1.2).1, (hIn A3.A.μ0 i.1.1 i.1.2).2, labIn_pairwise hi⟩) tie (Q, hy.choose) hy''
        have hm := (hTS _ hgc.1 hgc.2).1.1 (Finsupp.single (Formalism.IndefR.Links.labIn D.sp.X'.rank hy.choose) 1)
        refine hsys _ hgc.1 _ _ hm.choose_spec (Sum.inr (Q, y)) (hext _ _ fun f => ?_)
        exact (congrArg (R.jX A3.A.μ0) (LinearMap.congr_fun hy.choose_spec.2 f)).trans (h78.2.2.2 hX hXo f)
  exact ⟨fun i => (key i).choose, fun w hw i => (key i).choose_spec w hw⟩

end GlobalTheory.UpSystem
end

