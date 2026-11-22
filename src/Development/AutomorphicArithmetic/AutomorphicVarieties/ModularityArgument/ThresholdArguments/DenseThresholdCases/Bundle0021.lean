import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.SumTwoG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0007

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuSumTwoG
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open Module TensorProduct GlobalTheory.Pst.DpstMap
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Split
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
  {V₀ V₁ V₂ : Type} [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀]
  [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁]
  [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂]
  {ρ₀ : Representation ↥LL.1 ↥(GK K) V₀} {ρ₁ : Representation ↥LL.1 ↥(GK K) V₁}
  {ρ₂ : Representation ↥LL.1 ↥(GK K) V₂}
private theorem tensV_section (p : V₁ →ₗ[↥LL.1] V₂) (s : V₂ →ₗ[↥LL.1] V₁) (hps : ∀ v, p (s v) = v)
    (x : V₂ ⊗[ℚ_[l]] Bst P) : tensV P p (tensV P s x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hps]
  | add x y hx hy => simp only [map_add, hx, hy]
variable [FiniteDimensional ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₂]
private theorem isPst_split {AI : LocAinf l P} (T : LocTied l P AI) {i : V₀ →ₗ[↥LL.1] V₁} {p : V₁ →ₗ[↥LL.1] V₂}
    {s : V₂ →ₗ[↥LL.1] V₁} (hi : ∀ g v, i (ρ₀ g v) = ρ₁ g (i v)) (hp : ∀ g v, p (ρ₁ g v) = ρ₂ g (p v))
    (hs : ∀ g v, s (ρ₂ g v) = ρ₁ g (s v)) (h1 : Function.Injective i) (h2 : Function.Exact i p)
    (hps : ∀ v, p (s v) = v) (hV₀ : IsPst P ρ₀) (hV₂ : IsPst P ρ₂) : IsPst P ρ₁ := by
  obtain ⟨hdom, hfrac, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V₀ := Module.Finite.trans ↥LL.1 V₀
  haveI : FiniteDimensional ℚ_[l] V₁ := Module.Finite.trans ↥LL.1 V₁
  haveI : FiniteDimensional ℚ_[l] V₂ := Module.Finite.trans ↥LL.1 V₂
  have b₁ := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation P hdom hfrac ρ₁
  haveI f₁ : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁) :=
    Module.rank_lt_aleph0_iff.mp (b₁.trans_lt (Cardinal.natCast_lt_aleph0))
  obtain ⟨f₀, c₀⟩ := (isPst_iff P ρ₀).1 hV₀
  obtain ⟨f₂, c₂⟩ := (isPst_iff P ρ₂).1 hV₂
  obtain ⟨hinj, hex⟩ := UpperTheory.V.Loc.PstExact.dmap_exact P hi hp h1 h2
  have inj : Function.Injective (UpperTheory.V.Loc.PstExact.dUr P hi) := fun x y h => hinj h
  have sur : Function.Surjective (UpperTheory.V.Loc.PstExact.dUr P hp) := fun y =>
    ⟨toUr P ρ₁ (dmap P hs ((toUr P ρ₂).symm y)), Subtype.ext (tensV_section P p s hps _)⟩
  have ex : Function.Exact (UpperTheory.V.Loc.PstExact.dUr P hi) (UpperTheory.V.Loc.PstExact.dUr P hp) := fun y => hex y
  have e := (UpperTheory.V.Loc.PstExact.dUr P hp).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 sur, finrank_top, LinearMap.exact_iff.mp ex, LinearMap.finrank_range_of_inj inj] at e
  have e' := (p.restrictScalars ℚ_[l]).finrank_range_add_finrank_ker
  have exq : Function.Exact (i.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := h2
  rw [LinearMap.exact_iff.mp exq, LinearMap.finrank_range_of_inj (f := i.restrictScalars ℚ_[l]) h1,
    LinearMap.range_eq_top.2 (show Function.Surjective (p.restrictScalars ℚ_[l]) from fun v => ⟨s v, hps v⟩),
    finrank_top] at e'
  exact (isPst_iff P ρ₁).2 ⟨f₁, by omega⟩
end Split
section Sum
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a b : ℕ}
private theorem isPst_sum (T : LocTied l P AI) {L : FinExt l} (s : ↥Gw →* GL (Fin a) ↥L.1) (s' : ↥Gw →* GL (Fin b) ↥L.1)
    (h : IsPst P (Bw.repE L s)) (h' : IsPst P (Bw.repE L s')) : IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) := by
  let e : (Fin (a + b) → ↥L.1) ≃ₗ[↥L.1] (Fin a → ↥L.1) × (Fin b → ↥L.1) :=
    (LinearEquiv.funCongrLeft ↥L.1 ↥L.1 finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ ↥L.1 ↥L.1)
  have he : ∀ g v, e (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s') g v) =
      (Bw.repE L s g (e v).1, Bw.repE L s' g (e v).2) := by
    intro g v
    rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, GlobalTheory.BCGal.sumRep_val]
    ext i <;>
      simp [e, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl
  have he' : ∀ g x, e.symm (Bw.repE L s g x.1, Bw.repE L s' g x.2) =
      Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s') g (e.symm x) := by
    intro g x
    apply e.injective
    rw [he, e.apply_symm_apply, e.apply_symm_apply]
  refine isPst_split P T (i := e.symm.toLinearMap ∘ₗ LinearMap.inl ↥L.1 _ _)
    (p := LinearMap.snd ↥L.1 _ _ ∘ₗ e.toLinearMap) (s := e.symm.toLinearMap ∘ₗ LinearMap.inr ↥L.1 _ _)
    (ρ₀ := Bw.repE L s) (ρ₂ := Bw.repE L s') (fun g v => ?_) (fun g v => ?_) (fun g v => ?_) ?_ ?_ ?_ h h'
  · have := he' g (v, 0)
    simpa using this
  · simp [he]
  · have := he' g (0, v)
    simpa using this
  · intro x y hxy
    simpa using hxy
  · intro y
    constructor
    · intro hy
      refine ⟨(e y).1, ?_⟩
      apply e.injective
      have hy' : (e y).2 = 0 := hy
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply, e.apply_symm_apply]
      exact Prod.ext rfl hy'.symm
    · rintro ⟨x, rfl⟩
      simp
  · intro v
    simp
private theorem isPstAt_sum (T : LocTied l P AI) {r : ↥Gw →* GL (Fin a) (Om l)} {r' : ↥Gw →* GL (Fin b) (Om l)}
    (h : IsPstAt P Bw r) (h' : IsPstAt P Bw r') : IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
  obtain ⟨L₁, r₁, m₁, p₁⟩ := h
  obtain ⟨L₂, r₂, m₂, p₂⟩ := h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  exact ⟨supExt L₁ L₂, _, ⟨n₁.1, by rw [GlobalTheory.Pst.SumParam.mapRep_sumRep, n₁.2, n₂.2]⟩,
    isPst_sum Bw T _ _ (GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge P Bw l₁ r₁ p₁) (GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge P Bw l₂ r₂ p₂)⟩
end Sum
theorem UpperTheory.V.Z.Win.Gu.sumTwoG_of_printsH_gdLaws_sumAway_sumHTAt :
    _root_.UpperTheory.V.Af.HypothesesH' → GdLaws → SumAway → SumHTAt → SumTwoG := by
  intro _ hG hA hT E Ω _ _ _ _ _ l _ ι a b r r' p p' HT HT' C C'
  obtain ⟨T⟩ := Loc.tiedP l
  have hv := GlobalTheory.BCGal.cont_sumRep r r' (Units.continuous_val.comp C.cont) (Units.continuous_val.comp C'.cont)
  have hc : Continuous (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    simp only [← map_inv]
    exact hv.comp continuous_inv
  refine ⟨hc, GlobalTheory.BCGal.ss_sumRep r r' C.ss C'.ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩
  · exact hT E Ω l a b r r' C.cont C'.cont HT HT' w
      (C.ht w fun A h rc hrc => (((hG E Ω A w h).1 _ _).1 (hg A h rc hrc)).1)
      (C'.ht w fun A h rc hrc => (((hG E Ω A w h).1 _ _).1 (hg A h rc hrc)).2)
  · obtain ⟨a1, b1⟩ := C.par w A h rc hrc
    obtain ⟨a2, b2⟩ := C'.par w A h rc hrc
    have sp := ((hG E Ω A w h).1 (p w A h rc) (p' w A h rc)).1
    refine And.intro (fun hw => ?_) (fun O _ _ _ Bw hj hg => ?_)
    · obtain ⟨x, hx, kx⟩ := a1 hw
      obtain ⟨x', hx', kx'⟩ := a2 hw
      refine Exists.intro (x.lpSum x') (And.intro (hA E Ω l ι a b r r' C.cont C'.cont w hw A h _ _ hx hx') fun g => ?_)
      rw [kx (sp g).1, kx' (sp g).2]
    · obtain ⟨p1, e1⟩ := b1 O Bw hj (sp hg).1
      obtain ⟨p2, e2⟩ := b2 O Bw hj (sp hg).2
      have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (Dec (F := E) A).subtype =
          Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (Dec (F := E) A).subtype) (r'.comp (Dec (F := E) A).subtype) := by
        ext g i j
        rfl
      have p3 := isPstAt_sum Bw T p1 p2
      rw [e]
      exact ⟨p3, by rw [GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l _ _ ⟨T⟩ ι E Ω A w O Bw h hj a b _ _ p1 p2 p3, e1, e2]⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MPKapEx
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
namespace KapEx
end KapEx
open UpperTheory.V.Cu2.KapEx in
theorem kapEx_alt (h1 : TwistIne) (h2 : AlgType) : _root_.UpperTheory.V.Cu2.KapExAlt := by
  intro hP Ω _ _ _ l _ ι K' _ hl2 hK2 hTC hld hsp hcc
  obtain ⟨cc, hcc⟩ := hcc
  have : IsTotallyComplex K' := hTC
  have : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : IsGalois K' Ω := IsGalois.tower_top_of_isGalois ℚ K' Ω
  have : CompactSpace (G K' Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[K'] Ω))
  obtain ⟨κ₀, htw⟩ := _root_.UpperTheory.V.Sd.twist_of_printed_results hP K' Ω hK2 l hl2 hld ι cc hcc
  obtain ⟨art, Y, a, τ, hart, hYa, hL, ha1, ha0, -⟩ := htw.alg
  obtain ⟨mo, hmo0, -, hmo⟩ := htw.ord
  have hi : (galOf ℚ K' Ω).index = 2 := (galEmbTop ℚ K' Ω).2.2.trans hK2
  have hccK : cc ∉ galOf ℚ K' Ω := cc_notMem K' hcc
  have hfix : ∀ t : G ℚ Ω, t ∈ K'.fixingSubgroup → t ∈ galOf ℚ K' Ω := fun t h =>
    (mem_galOf ℚ K' Ω).2 fun x => (IntermediateField.mem_fixingSubgroup_iff K' t).1 h x x.2
  have hIne : ∀ (A : ValuationSubring Ω) (h : G K' Ω), resQ K' h ∈ Ine (F := ℚ) A → h ∈ Ine (F := K') A :=
    fun A h hh => ⟨hh.1, hh.2⟩
  have hεc : Continuous (cycBar K' Ω l) := by
    have hf : Continuous (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom : ℤ_[l] → Qbar l) :=
      (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
    exact (Units.continuous_map hf).comp (continuous_cycZ K' Ω l)
  have hεunr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ h ∈ Ine (F := K') A, cycBar K' Ω l h = 1 := by
    intro A hA h hh
    have e : cycZ K' Ω l h = 1 := MonoidHom.mem_ker.1 (((places K' Ω l A).2.2.2 hA) hh)
    simp only [cycBar, MonoidHom.comp_apply, e, map_one]
  have hεres : ∀ h : G K' Ω, cycBar K' Ω l h = cycBar ℚ Ω l (resQ K' h) := fun h => rfl
  have hlam : ∀ h : G K' Ω, (κ₀ ^ 2 * cycBar K' Ω l) h = κ₀ h ^ 2 * cycBar K' Ω l h := fun h => by
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply]
  have hlamc : Continuous ⇑(κ₀ ^ 2 * cycBar K' Ω l : G K' Ω →* (Qbar l)ˣ) := by
    have e : ⇑(κ₀ ^ 2 * cycBar K' Ω l : G K' Ω →* (Qbar l)ˣ) = fun h => κ₀ h ^ 2 * cycBar K' Ω l h := funext hlam
    rw [e]
    exact (htw.cont.pow 2).mul hεc
  obtain ⟨d, hd0, hd⟩ := exists_pow_cong _ hlamc
  refine ⟨d * mo, (κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo), fun j hj => ?_⟩
  rw [← pow_mul]
  have hN : 0 < d * mo * j := Nat.mul_pos (Nat.mul_pos hd0 hmo0) (by omega)
  obtain ⟨Y', hY', hL'⟩ := h2 K' Ω l ι art Y a κ₀ hart hYa hL (2 * (d * mo * j)) (d * mo * j)
  have hpw : (κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo * j) =
      κ₀ ^ (2 * (d * mo * j)) * cycBar K' Ω l ^ (d * mo * j) := by
    rw [mul_pow, ← pow_mul]
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : ⇑((κ₀ ^ 2 * cycBar K' Ω l) ^ (d * mo * j) : G K' Ω →* (Qbar l)ˣ) = fun h => (κ₀ h ^ 2 * cycBar K' Ω l h) ^ (d * mo * j) :=
      funext fun h => by rw [MonoidHom.pow_apply, hlam]
    rw [e]
    exact ((htw.cont.pow 2).mul hεc).pow _
  · refine ⟨art, Y', _, τ, hart, hY', by rw [hpw]; exact hL', ?_, ?_⟩
    · show ((2 * (d * mo * j) : ℕ) : ℤ) * a τ + ((d * mo * j : ℕ) : ℤ) = -((d * mo * j : ℕ) : ℤ)
      rw [ha1]
      push_cast
      ring
    · show ((2 * (d * mo * j) : ℕ) : ℤ) * a (ComplexEmbedding.conjugate τ) + ((d * mo * j : ℕ) : ℤ) = ((d * mo * j : ℕ) : ℤ)
      rw [ha0]
      push_cast
      ring
  · intro t ht h h' hh'
    have htg : t ∉ galOf ℚ K' Ω := fun h0 => ht (by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (mem_galOf ℚ K' Ω).1 h0 ⟨x, hx⟩)
    have hu : cc⁻¹ * t ∈ galOf ℚ K' Ω := by
      rw [Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff]
      exact iff_of_false hccK htg
    rw [← range_galEmb] at hu
    obtain ⟨v, hv⟩ := hu
    have hh'' : galEmb ℚ K' Ω h' = t * galEmb ℚ K' Ω h * t⁻¹ := hh'
    have hs : galEmb ℚ K' Ω h' = cc * galEmb ℚ K' Ω (v * h * v⁻¹) * cc⁻¹ := by
      rw [map_mul, map_mul, map_inv, hv, hh'']
      group
    have hc := htw.conj (v * h * v⁻¹) h' hs
    simp only [map_mul, map_inv, mul_inv_cancel_comm] at hc
    have hε' : cycBar K' Ω l h' = cycBar K' Ω l h := by
      rw [hεres, hεres h, hh', map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, ← mul_pow, hlam, hlam, hε', mul_mul_mul_comm, ← mul_pow, hc,
      ← sq (cycBar K' Ω l h), inv_pow, inv_mul_cancel, one_pow]
  · intro t ht h hh
    have htg : t ∉ galOf ℚ K' Ω := fun h0 => ht (by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (mem_galOf ℚ K' Ω).1 h0 ⟨x, hx⟩)
    have e1 := htw.ver h t htg hh
    have e2 : cycBar K' Ω l h = cycBar ℚ Ω l t * cycBar ℚ Ω l t := by
      rw [hεres, hh, map_mul]
    rw [MonoidHom.pow_apply, hlam, e1, e2, neg_sq, inv_pow, ← sq (cycBar ℚ Ω l t), inv_mul_cancel, one_pow]
  · intro h
    apply cong_of_mem
    rw [MonoidHom.pow_apply, pow_mul, pow_mul]
    exact pow_mem (pow_mem (hd h) mo) j
  · intro A hA h hh
    have h' := hIne A h hh
    rw [MonoidHom.pow_apply, hlam, hεunr A hA h h', mul_one, ← pow_mul,
      show 2 * (d * mo * j) = mo * (2 * d * j) by ring, pow_mul, hmo A hA h h', one_pow]
  · intro A hA
    rcases h1 Ω l ι K' hK2 hTC hld hsp cc κ₀ htw A hA with e | e
    · refine Or.inr fun h hh => ?_
      rw [MonoidHom.pow_apply, hlam, e h (hIne A h hh), zpow_neg, zpow_natCast, sq, mul_assoc, inv_mul_cancel, mul_one,
        inv_pow]
    · refine Or.inl fun h hh => ?_
      rw [MonoidHom.pow_apply, hlam, e h (hIne A h hh), one_pow, one_mul, zpow_natCast]
end UpperTheory.V.Cu2
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MPTauEx
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
private theorem ce_char {l : ℕ} [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (ka : Γ →* (PadicAlgCl l)ˣ) (h : Continuous ka) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ g, (ka g).val ∈ E ∧ ‖(ka g).val‖ ≤ 1 := by
  have hc : Continuous fun g => (ka g).val := Units.continuous_val.comp h
  let r : Γ →* GL (Fin 1) (PadicAlgCl l) :=
    (Units.map (Matrix.scalar (Fin 1) : PadicAlgCl l →+* _).toMonoidHom).comp ka
  have hr : ∀ (g : Γ) (i j : Fin 1), (r g).val i j = (ka g).val := by
    intro g i j
    obtain rfl : i = j := Subsingleton.elim _ _
    simp [r]
  obtain ⟨E, hE, hm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 1 r
    (fun i j => by simp only [hr]; exact hc)
  refine ⟨E, hE, fun g => ⟨hr g 0 0 ▸ hm g 0 0, ?_⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_range hc.norm).bddAbove
  by_contra hg
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C (not_le.1 hg)
  have := hC ⟨g ^ N, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hN (not_lt.2 this)
theorem tauEx' (h1 : _root_.UpperTheory.V.Cu2.KapExAlt) (h2 : TauOf) : _root_.UpperTheory.V.Cu.TauExAlt := by
  intro hP Ω _ _ _ l _ ι K' _ hl2 hK hTC hdisc hdec hcc g0 hg0
  obtain ⟨m, κ, hκ⟩ := h1 hP Ω l ι K' hl2 hK hTC hdisc hdec hcc
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsGalois K' Ω := IsGalois.tower_top_of_isGalois ℚ K' Ω
  haveI : CompactSpace (G K' Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[K'] Ω))
  haveI : T2Space (G K' Ω) := inferInstanceAs (T2Space (Ω ≃ₐ[K'] Ω))
  have hc : Continuous κ := by simpa using (hκ 1 le_rfl).cont
  obtain ⟨E, hE, hmE⟩ := ce_char (G K' Ω) κ hc
  haveI := hE
  obtain ⟨c₁, hc₁⟩ := UpperTheory.V.X.So.coefOf l E
  refine ⟨m, c₁, κ, fun c₂ hc₂ j hj => ?_⟩
  refine h2 Ω l ι K' hl2 hK hdec g0 hg0 (m * j) (κ ^ j) (hκ j hj) c₂ fun h => ?_
  have e : (((κ ^ j) h : (Qbar l)ˣ) : Qbar l) = ((κ h : (Qbar l)ˣ) : Qbar l) ^ j := by
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  rw [e]
  exact pow_mem (hc₂ ((hc₁ _).2 (hmE h))) j
end UpperTheory.V.Cu2
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MemOfNormVDvd
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
open UpperTheory.V UpperTheory.V.Af
open scoped Matrix
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform
local instance (priority := high + 1)  (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] :
    Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree
private theorem cofinite_notMem (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw
private theorem mem_of_normV_dvd {N : ℕ} {w : HeightOneSpectrum (𝓞 ℚ)} (h : normV w ∣ N) :
    ((N : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
  obtain ⟨c, rfl⟩ := h
  have e : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [Nat.cast_mul, e]
  exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)
private theorem charpoly_scale {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (B : Multiset ℂ)
    (h : M.charpoly.map φ = (B.map fun b => X - C b).prod) :
    (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod := by
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by linear_combination e0
  have ht : φ M.trace = x + y := by linear_combination e0 - e1
  simp only [hd, ht, C_add, C_mul]
  ring
private theorem scale_sat {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (B : Multiset ℂˣ) (q : ℕ)
    (u : ℂˣ) (hu : φ c = u) (P Q : ℂ[X]) (h : M.charpoly.map φ = P)
    (hP : ((algSat 2 q B).map fun b => X - C ((q : ℂ) ^ (0 : ℤ) * b)).prod = P)
    (hQ : ((algSat 2 q (B.map (· * u))).map fun b => X - C ((q : ℂ) ^ (0 : ℤ) * b)).prod = Q) :
    (c • M).charpoly.map φ = Q := by
  simp only [zpow_zero, one_mul] at hP hQ
  rw [charpoly_scale φ M c (algSat 2 q B) (h.trans hP.symm), ← hQ, hu]
  simp only [algSat, Multiset.bind_singleton, Multiset.map_map, Multiset.pure_def, Multiset.bind_def]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply, Units.val_mul]
  ring_nf
private theorem ss_twist {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep r) : IsSSRep (tw r χ) := by
  have key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W := fun W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((key W).1 hW)
  exact ⟨W', (key W').2 hW', hc⟩
private theorem isOpen_ker {Ω C : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Group C] {N : ℕ} (hN : 1 ≤ N)
    {κ : G ℚ Ω →* C} (hκ : KillsMu N κ) : IsOpen (κ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ N = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots N (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hN] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hκ s fun ζ hζ => hs ζ hζ
theorem exists_newform_attached_twist_of_kills_mu (P : _root_.UpperTheory.V.Af.HypothesesH') {k : ℕ} (hk : 2 ≤ k) (f : Newform k) {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hf : f.Att ι V)
    (κ : G ℚ Ω →* (Qbar l)ˣ) {N : ℕ} (hN : 1 ≤ N) (hκ : KillsMu N κ) :
    ∃ g : Newform k, g.Att ι (tw V κ) := by
  obtain ⟨art, ha⟩ : ∃ art : Neutral.B1.Ideles ℚ →* Gab ℚ Ω, IsGlobalArtin art := P.toClassicalTheorems.litN.aut.art _ Ω
  have ho := isOpen_ker hN hκ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hfi : Finite (G ℚ Ω ⧸ κ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hm : 0 < κ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨χ, ⟨h1, hL⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι κ (continuous_of_isOpen_ker' κ ho) hm
    (MonoidHom.ext fun s => by
      rw [MonoidHom.pow_apply, ← map_pow]
      exact κ.ker.pow_index_mem s)
  have hexpo : ∀ v, TR.expo χ v = 0 := GlobalTheory.HenQ.expo_eq_zero_of_pow χ hm h1
  obtain ⟨π, hinf, hsat⟩ := P.toClassicalTheorems.newform k hk f 0
  obtain ⟨g, hg⟩ := UpperTheory.V.Af.repNewform k hk 0 (π.twist χ) fun v => by
    have := (hinf v).twist χ
    rw [hexpo v] at this
    simpa using this
  refine ⟨g, ss_twist _ _ hf.1, ?_⟩
  filter_upwards [hf.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ), cofinite_notMem l hl.out.ne_zero,
    cofinite_notMem f.M f.pos.ne', cofinite_notMem g.M g.pos.ne'] with w hw hu hwl hwf hwg A hA
  obtain ⟨B, hB, hpB⟩ := hsat w fun h => hwf (mem_of_normV_dvd h)
  obtain ⟨S, hS, hpS⟩ := hg w fun h => hwg (mem_of_normV_dvd h)
  obtain rfl : S = B.map (· * χ.val w) := hS.unique (hB.twist hu)
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have e1 : κ s = 1 := (hL.unr_iff ha (Or.inl hwl) hA).2 hu s hs
    apply Units.ext
    rw [tw_val, e1, (hw A hA).1 s hs, Units.val_one, one_smul, Units.val_one]
  · have e1 : ι.toRingHom ((κ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (χ.val w : ℂ) := by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inl hwl) hu hA hσ, inv_inv]
      exact ι.apply_symm_apply _
    rw [tw_val]
    exact scale_sat ι.toRingHom _ _ B _ _ e1 _ _ ((hw A hA).2 σ hσ) hpB hpS
end UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform
open UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform in
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.twNew_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → GlobalTheory.Ord2.TwNewQ := by
  intro P l _ Ω _ _ _ ι e W _ he hA M φ hM hφ
  obtain ⟨f, M', φ', hM', hφ', hf⟩ := hA.modular
  have hMM : 1 ≤ M * M' := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hκ : KillsMu (M * M') (φ * φ'⁻¹) := fun s hs => by
    have h1 : φ s = 1 := hφ s fun ζ hζ => hs ζ (by rw [pow_mul, hζ, one_pow])
    have h2 : φ' s = 1 := hφ' s fun ζ hζ => hs ζ (by rw [mul_comm, pow_mul, hζ, one_pow])
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, h2, inv_one, one_mul]
  obtain ⟨g, hg⟩ := _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform.exists_newform_attached_twist_of_kills_mu P (by omega) f ι _ hf (φ * φ'⁻¹) hMM hκ
  refine ⟨g, ?_⟩
  convert hg using 1
  ext1 s
  apply Units.ext
  simp only [tw_val, smul_smul, MonoidHom.mul_apply, MonoidHom.inv_apply, ← Units.val_mul]
  congr 2
  rw [mul_comm (φ s) (φ' s)⁻¹, mul_assoc, ← mul_assoc (φ s), mul_comm _ (φ' s), inv_mul_cancel_left, mul_comm]
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NumJ
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ)
  (lam : Wt L l n) (K : H.Lev) (P : (H.Gq →* GL (Fin n) (Qbar l)) → Prop)
end
def NumJAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 → ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (B : W.UniversalOrdinaryDeterminantRing r)
    (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev) (J : Ideal B.B), r.V0ok → IsDomain Λ.Λ → R.IsJ B K J → J.IsRadical →
    UpperTheory.V.J.Num B Λ J
end UpperTheory.V.Z.J.D
end
end
end

