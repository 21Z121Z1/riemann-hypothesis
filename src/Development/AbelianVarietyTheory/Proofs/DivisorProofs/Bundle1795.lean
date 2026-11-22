import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0102
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqVolumeSumCharacterTwistedCosets
section
open MeasureTheory

namespace GlobalTheory.TwistedCosetSum

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem coset_integral [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableAdd X] (μ : Measure X)
    [μ.IsAddLeftInvariant] (U : AddSubgroup X) (hU : IsOpen (U : Set X)) (g : X → ℂ)
    (hg : ∀ y, ∀ u ∈ U, ∀ u' ∈ U, g (y + u + u') * g y = g (y + u) * g (y + u')) (c : X) :
    ∫ y, ((fun x => -c + x) ⁻¹' (U : Set X)).indicator g y ∂μ = 0 ∨
    ∫ y, ((fun x => -c + x) ⁻¹' (U : Set X)).indicator g y ∂μ = g c * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  classical
  set S : Set X := (fun x => -c + x) ⁻¹' (U : Set X) with hS
  have hmem : ∀ y, y ∈ S ↔ -c + y ∈ U := fun y => Iff.rfl
  have hmeas : MeasurableSet S := (hU.preimage (continuous_const.add continuous_id)).measurableSet
  have hvol : μ S = μ U := measure_preimage_add μ _ _
  by_cases h : ∀ u ∈ U, g (c + u) = g c
  · right
    have : S.indicator g = S.indicator (fun _ => g c) := by
      refine Set.indicator_congr fun y hy => ?_
      have := h _ ((hmem y).1 hy)
      rwa [add_neg_cancel_left] at this
    rw [this, integral_indicator_const _ hmeas]
    simp only [Measure.real, hvol, Complex.real_smul]
    ring
  · left
    push_neg at h
    obtain ⟨u, hu, hne⟩ := h
    have hc0 : g c ≠ 0 := by
      intro h0
      have := hg c u hu u hu
      rw [h0, mul_zero] at this
      exact hne (by rw [h0]; exact mul_self_eq_zero.1 this.symm)
    have hshift : ∀ y, S.indicator g (u + y) * g c = g (c + u) * S.indicator g y := by
      intro y
      have hiff : u + y ∈ S ↔ y ∈ S := by
        rw [hmem, hmem, add_left_comm]
        exact U.add_mem_cancel_left hu
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hiff.2 hy)]
        have := hg c u hu _ ((hmem y).1 hy)
        rw [add_neg_cancel_left, show c + u + (-c + y) = u + y by abel] at this
        exact this
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (hiff.1 h)), zero_mul, mul_zero]
    have h1 : (∫ y, S.indicator g y ∂μ) * g c = g (c + u) * ∫ y, S.indicator g y ∂μ := by
      conv_lhs => rw [← integral_add_left_eq_self (μ := μ) (S.indicator g) u]
      rw [← integral_mul_const, ← integral_const_mul]
      simp only [hshift]
    have h2 : (g (c + u) - g c) * ∫ y, S.indicator g y ∂μ = 0 := by
      rw [sub_mul, ← h1]; ring
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)

theorem integral_eq_sum_twisted : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant] (U : AddSubgroup X), IsOpen (U : Set X) → μ (U : Set X) ≠ ⊤ →
    ∀ g : X → ℂ, HasCompactSupport g → (∀ y, ∀ u ∈ U, ∀ u' ∈ U, g (y + u + u') * g y = g (y + u) * g (y + u')) →
    ∃ s : Finset X, ∫ y, g y ∂μ = (∑ γ ∈ s, g γ) * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  intro X _ _ _ _ _ _ μ _ U hU _ g hc hg
  classical
  by_cases hint : Integrable g μ
  swap
  · exact ⟨∅, by rw [integral_undef hint]; simp⟩
  haveI := GlobalTheory.LCIntegralField.discrete_quot U hU
  have hfin : ((QuotientAddGroup.mk : X → X ⧸ U) '' tsupport g).Finite :=
    (hc.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T := hfin.toFinset with hT
  have hind : ∀ (c : X ⧸ U) y, (-(Quotient.out c) + y ∈ U ↔ c = (y : X ⧸ U)) := by
    intro c y
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  have hdec : g = fun y => ∑ c ∈ T,
      ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator g y := by
    funext y
    have key : ∀ c : X ⧸ U, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator
        g y = if c = (y : X ⧸ U) then g y else 0 := by
      intro c
      by_cases h : c = (y : X ⧸ U)
      · rw [if_pos h, Set.indicator_of_mem (show y ∈ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from (hind c y).2 h)]
      · rw [if_neg h, Set.indicator_of_notMem (show y ∉ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from fun hm => h ((hind c y).1 hm))]
    simp only [key]
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · rw [hT, Set.Finite.mem_toFinset] at hmem
      exact image_eq_zero_of_notMem_tsupport (fun hs => hmem ⟨y, hs, rfl⟩)
  have hmeas : ∀ c : X ⧸ U, MeasurableSet ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)) := fun c =>
    (hU.preimage (continuous_const.add continuous_id)).measurableSet
  have hsum : ∫ y, g y ∂μ = ∑ c ∈ T, ∫ y, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator g y ∂μ := by
    rw [← integral_finset_sum _ fun c _ => hint.indicator (hmeas c)]
    exact congrArg _ hdec
  refine ⟨(T.filter fun c => ∫ y, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator g y ∂μ ≠ 0).image
    Quotient.out, ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => Quotient.out_injective h), hsum, ← Finset.sum_filter_ne_zero,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun c hc => ?_
  exact (coset_integral μ U hU g hg (Quotient.out c)).resolve_left (Finset.mem_filter.1 hc).2

end GlobalTheory.TwistedCosetSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointsIndicatorFourierSelfUnramified
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.RatWeilOp

theorem ind_fourier_self : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    μ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 → (fun y : κ → Fv F v => ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ) = ind κ v := by
  intro F _ _ v ψ hψ κ _ _ _ μ _ hμ
  classical
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hSo : IsOpen {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
    have e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
        ⋂ i, (fun x : κ → Fv F v => x i) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext; simp
    rw [e]; exact isOpen_iInter_of_finite fun i => hO.preimage (continuous_apply i)
  have hSm := hSo.measurableSet
  have hψO : ∀ z ∈ v.adicCompletionIntegers F, ψ z = 1 := fun z hz => by
    simpa using (hψ 1).2 (v.adicCompletionIntegers F).one_mem z hz
  have hdot : ∀ x y : κ → Fv F v, (∀ i, x i ∈ v.adicCompletionIntegers F) → (∀ i, y i ∈ v.adicCompletionIntegers F) →
      x ⬝ᵥ y ∈ v.adicCompletionIntegers F := fun x y hx hy =>
    (v.adicCompletionIntegers F).sum_mem fun i _ => mul_mem (hx i) (hy i)
  funext y
  by_cases hy : ∀ i, y i ∈ v.adicCompletionIntegers F
  · have e : (fun x => ind κ v x * ψ (x ⬝ᵥ y)) =
        Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
      · have hx' : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_mem hx', Pi.one_apply, one_mul, hψO _ (hdot x y hx hy)]
      · have hx' : x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_notMem hx', zero_mul]
    have hy' : y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hy
    rw [e, integral_indicator hSm, setIntegral_const, Measure.real, hμ]
    simp [ind, Set.indicator_of_mem hy']
  · have hy' : y ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hy
    have h0 : ind κ v y = 0 := by simp only [ind, Set.indicator_of_notMem hy']
    rw [h0]
    push_neg at hy
    obtain ⟨i, hi⟩ := hy
    have : ¬ ∀ t ∈ v.adicCompletionIntegers F, ψ (y i * t) = 1 := fun h => hi ((hψ (y i)).1 h)
    push_neg at this
    obtain ⟨t, ht, hne⟩ := this
    have hs : ∀ j, (Pi.single i t : κ → Fv F v) j ∈ v.adicCompletionIntegers F := fun j => by
      by_cases hj : j = i
      · subst hj; simpa using ht
      · simp [Pi.single_apply, hj]
    have hind : ∀ x, ind κ v (Pi.single i t + x) = ind κ v x := fun x => by
      have : (∀ j, ((Pi.single i t : κ → Fv F v) + x) j ∈ v.adicCompletionIntegers F) ↔ ∀ j, x j ∈ v.adicCompletionIntegers F := by
        constructor
        · intro h j
          have := sub_mem (h j) (hs j)
          simpa using this
        · intro h j
          exact add_mem (hs j) (h j)
      by_cases hx : ∀ j, x j ∈ v.adicCompletionIntegers F
      · have h1 : Pi.single i t + x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := this.2 hx
        have h2 : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply]
      · have h1 : Pi.single i t + x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := fun h => hx (this.1 h)
        have h2 : x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    have key : ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ = ψ (y i * t) * ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ := by
      rw [← integral_const_mul]
      conv_lhs => rw [← integral_add_left_eq_self (μ := μ) (fun x => ind κ v x * ψ (x ⬝ᵥ y)) (Pi.single i t)]
      congr 1
      funext x
      rw [hind, add_dotProduct, single_dotProduct, AddChar.map_add_eq_mul, mul_comm t (y i)]
      ring
    have h1 : (1 - ψ (y i * t)) * ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (Ne.symm hne))

end GlobalTheory.RatWeilOp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicColimitOfIsNilpotent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorusModel GlobalTheory.AdicColimit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

def pushEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y =>
    ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem actPull_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] [IsCommMonObj G] {Λ : Type} [Ring Λ]
    (ρ : RingAct G Λ) (a : Λ) :
    ((actPull f ρ).act a).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ (ρ.act a).left :=
  pullback.lift_fst _ _ _

variable {p : ℕ} {R : Type} [CommRing R] {I : Ideal R} {O : Type} [CommRing O]

theorem isAdicColimit_of_isNilpotent {f : R →+* O} (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    (S : Type) [CommRing S] [Algebra O S] (hS : IsNilpotent (p : S)) :
    IsAdicColimit I (Over.mk ((specO O S).hom ≫ spMap f)) := by
  obtain ⟨n, hn⟩ := hf
  obtain ⟨m, hm⟩ := hS
  have e : (specO O S).hom ≫ spMap f = Spec.map (CommRingCat.ofHom ((algebraMap O S).comp f)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  rw [e]
  refine isAdicColimit_of_pow I _ (n * m) fun a ha => ?_
  have h₁ : (I ^ n).map f ≤ Ideal.span {(p : O)} := Ideal.map_le_iff_le_comap.2 hn
  have h₂ : f a ∈ Ideal.span {(p : O) ^ m} := by
    rw [← Ideal.span_singleton_pow]
    refine Ideal.pow_right_mono h₁ m ?_
    rw [← Ideal.map_pow, ← pow_mul]
    exact Ideal.mem_map_of_mem f ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h₂
  rw [RingHom.comp_apply, ← hc, map_mul, map_pow, map_natCast, hm, mul_zero]

variable [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} [Algebra O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ]

theorem spMap_comp_algebraMap (f : R →+* O) :
    spMap ((algebraMap O C).comp f) = spMap (algebraMap O C) ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

def ofCompletion (hv : v.Integers O) (ε : Eps p C) (f : R →+* O)
    (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (ιG : RingAct G Λ)
    {E : SplitExt (Sp R)} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H] (d : E.GtDatum H) (ρ : RingAct H Λ)
    (J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G)))
    (hnat : ∀ T T' hT hT' (k : T' ⟶ T) (x : T ⟶ H), J T' hT' (k ≫ x) = k ≫ J T hT x)
    (hlin : ∀ T hT (x : T ⟶ H) (a : Λ), J T hT (x ≫ ρ.act a) = J T hT x ≫ ιG.act a)
    (A' : PolAV (Sp C)) (oA' : A'.OAct Λ) (j : A'.A.left ⟶ G.left)
    (hj : IsGrpPullback A'.A G (spMap ((algebraMap O C).comp f)) j)
    (hact : ∀ a, (oA'.act a).left ≫ j = j ≫ (ιG.act a).left) : Point p v O Λ where
  integers := hv
  eps := ε
  A := A'
  oA := oA'
  G := (Over.pullback (spMap f)).obj G
  semi := IsSemiAbelian.pullback _ G hG
  gen := pullback.lift j (A'.A.hom ≫ spMap (algebraMap O C))
    (by rw [hj.1.w, spMap_comp_algebraMap, Category.assoc])
  gen_pull := (isGrpPullback_pullback G (spMap f)).cancel
    (hj.congr (spMap_comp_algebraMap f) (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  oG := actPull (spMap f) ιG
  gen_act a := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hact, Category.assoc, actPull_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, pullback.lift_snd, Over.w_assoc, Category.assoc]
      exact ((congrArg (_ ≫ ·) (Over.w ((actPull (spMap f) ιG).act a))).trans (pullback.lift_snd _ _ _)).symm
  Ext := GtBaseChange.extBC (spMap f) E
  Gt := (Over.pullback (spMap f)).obj H
  D := (GtBaseChange.isGt_extBC (spMap f) E H d).some
  oGt := actPull (spMap f) ρ
  cmp S _ _ hS := (pushEquiv (isGrpPullback_pullback H (spMap f)) _).trans
    ((J _ (isAdicColimit_of_isNilpotent hf S hS)).trans (pushEquiv (isGrpPullback_pullback G (spMap f)) _).symm)
  cmp_nat S S' _ _ _ _ hS hS' φ x := by
    let k : Over.mk ((specO O S').hom ≫ spMap f) ⟶ Over.mk ((specO O S).hom ≫ spMap f) :=
      Over.homMk (ptMap φ).left (Over.w_assoc (ptMap φ) _)
    have e : ∀ {X : Over (Sp R)} [GrpObj X] (y : specO O S ⟶ (Over.pullback (spMap f)).obj X),
        pushEquiv (isGrpPullback_pullback X (spMap f)) _ (ptMap φ ≫ y) =
          k ≫ pushEquiv (isGrpPullback_pullback X (spMap f)) _ y := fun y =>
      Over.OverMorphism.ext (Category.assoc _ _ _)
    simp only [MulEquiv.trans_apply]
    rw [MulEquiv.symm_apply_eq, e, e, MulEquiv.apply_symm_apply, hnat]
  cmp_act S _ _ hS a x := by
    have e : ∀ {X : Over (Sp R)} [GrpObj X] [IsCommMonObj X] (α : RingAct X Λ)
        (y : specO O S ⟶ (Over.pullback (spMap f)).obj X),
        pushEquiv (isGrpPullback_pullback X (spMap f)) _ (y ≫ (actPull (spMap f) α).act a) =
          pushEquiv (isGrpPullback_pullback X (spMap f)) _ y ≫ α.act a := fun α y =>
      Over.OverMorphism.ext ((Category.assoc _ _ _).trans
        ((congrArg (y.left ≫ ·) (actPull_fst _ α a)).trans (Category.assoc _ _ _).symm))
    simp only [MulEquiv.trans_apply]
    rw [MulEquiv.symm_apply_eq, e, e, MulEquiv.apply_symm_apply, hlin]

section Unif

variable [IsDomain R] {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G)

theorem exists_comparison : ∃ (H : Over (Sp R)) (_ : GrpObj H) (_ : IsCommMonObj H)
    (Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T) (J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G))),
    (splitExt D.toPre).IsGt H ∧ Represents Φ ∧
      (∀ T hT w x, J T hT w = x ↔ FormalPoint.IsPointOf U (Φ T w) x) ∧
      ∀ T T' hT hT' (k : T' ⟶ T) (x : T ⟶ H), J T' hT' (k ≫ x) = k ≫ J T hT x := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL (splitExt D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL hH
  obtain ⟨J, hJ⟩ := exists_mulEquiv U hL (Φ := Φ) hΦ
  exact ⟨H, inferInstance, inferInstance, Φ, J, hH, hΦ, hJ, fun T T' hT hT' k x =>
    (hJ _ hT' _ _).2 (((hJ _ hT x _).1 rfl).pull k (hΦ.1 _ _ k _))⟩

theorem exists_point_of_unif (hG : IsSemiAbelian G) [Module Λ D.toPre.X] {ιD : D.OAct Λ} {ιA : A.OAct Λ}
    {ιG : RingAct G Λ} (hO : U.OLinear Λ ιD ιA ιG) (hv : v.Integers O) (ε : Eps p C) (f : R →+* O)
    (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    (A' : PolAV (Sp C)) (oA' : A'.OAct Λ) (j : A'.A.left ⟶ G.left)
    (hj : IsGrpPullback A'.A G (spMap ((algebraMap O C).comp f)) j)
    (hact : ∀ a, (oA'.act a).left ≫ j = j ≫ (ιG.act a).left) :
    ∃ (H : Over (Sp R)) (_ : GrpObj H) (_ : IsCommMonObj H) (Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T)
      (ρ : RingAct H Λ) (P : Point p v O Λ),
      (splitExt D.toPre).IsGt H ∧ Represents Φ ∧
      (∀ (a : Λ) T (x : T ⟶ H), FormalPoint.IsSmulPt ιD a (Φ T x) (Φ T (x ≫ ρ.act a))) ∧
      P.eps = ε ∧ P.A = A' ∧ HEq P.oA oA' ∧ P.G = (Over.pullback (spMap f)).obj G ∧
      P.Ext = GtBaseChange.extBC (spMap f) (splitExt D.toPre) ∧ P.Gt = (Over.pullback (spMap f)).obj H ∧
      ∃ (πG : P.G.left ⟶ G.left) (πH : P.Gt.left ⟶ H.left) (hπG : IsGrpPullback P.G G (spMap f) πG)
        (hπH : IsGrpPullback P.Gt H (spMap f) πH),
        HEq πG (pullback.fst G.hom (spMap f)) ∧ HEq πH (pullback.fst H.hom (spMap f)) ∧
        HEq (P.gen ≫ πG) j ∧
        (∀ a, (P.oG.act a).left ≫ πG = πG ≫ (ιG.act a).left) ∧
        (∀ a, (P.oGt.act a).left ≫ πH = πH ≫ (ρ.act a).left) ∧
        ∀ (S : Type) [CommRing S] [Algebra O S] (hS : IsNilpotent (p : S)) (x : specO O S ⟶ P.Gt),
          FormalPoint.IsPointOf U (Φ _ (pushPt hπH.1.w x)) (pushPt hπG.1.w (P.cmp S hS x)) := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, Φ, J, ⟨d⟩, hΦ, hJ, hnat⟩ := exists_comparison U
  obtain ⟨ρ, hρ⟩ := exists_ringAct hL ιD (Φ := Φ) hΦ
  refine ⟨H, inferInstance, inferInstance, Φ, ρ, ofCompletion hv ε f hf hG ιG d ρ J hnat
      (fun T hT x a => (hJ _ hT _ _).2 (((hJ _ hT x _).1 rfl).smul hL hO a (hρ a _ _))) A' oA' j hj hact,
    ⟨d⟩, hΦ, hρ, rfl, rfl, HEq.rfl, rfl, rfl, rfl, _, _, isGrpPullback_pullback G _, isGrpPullback_pullback H _,
    HEq.rfl, HEq.rfl, heq_of_eq (pullback.lift_fst _ _ _), actPull_fst _ ιG, actPull_fst _ ρ, fun S _ _ hS x => ?_⟩
  exact (hJ _ (isAdicColimit_of_isNilpotent hf S hS) _ _).1
    ((pushEquiv (isGrpPullback_pullback G (spMap f)) _).apply_symm_apply _).symm

end Unif

end GlobalTheory.HTLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
section
noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG)
open GlobalTheory.NormDict

namespace GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsScale (D : D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) : Prop :=
  r * D.host.conj r * ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E)

def coordY (θ : InfFam D) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ) (r : D.host.E) (w : WO S T) :
    VC D a d :=
  fun τ i j => δ * embT D τ r * compAt θ τ w (Fin.cast hT.symm i) (Fin.cast hS.symm j)

def Reads (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E) (G : VC D a d → ℂ) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ w : WO S T, w.map (finPart D) = 0 →
    f w = Complex.exp (-((Real.pi : ℂ) / 2) * Hf D (tor0 D cc δ) (coordY θ hS hT δ r w) (coordY θ hS hT δ r w)) *
      G (coordY θ hS hT δ r w)

structure Setup (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E) :
    Prop where
  std : IsStdChar D ψ (-1)
  inf : IsInfFam θ
  gS : S.gram = 1
  gT : T.gram = 1
  crv : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ
  scale : IsScale D cc r

def finPt {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (r : D.host.E) (z : Matrix (Fin d) (Fin a) D.host.E) :
    WO S T :=
  GlobalTheory.VacUnique.finRat S T (Matrix.of fun i j => -(r⁻¹ * z (Fin.cast hT i) (Fin.cast hS j)))

def IsFinIdl (x : (AE D)ˣ) (y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) = GlobalTheory.BotFormula.toFinE D (y : Formalism.MainNotions.StandardLatticesGL3.AE D)

def HasFinPart (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ) : Prop :=
  ∀ x y, IsFinIdl x y → ((χ x : Circle) : ℂ) = ((c.f y ^ e : ℂˣ) : ℂ)

def IsCongLevel {N : ℕ} (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D N)) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∀ k ∈ intG D N, (∀ i j, ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D,
    (((k : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j =
      (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * s) → k ∈ J

def period (D : D7) (δ : ℂ) (r : D.host.E) (τ : D.what₂.Tau) : ℂ :=
  δ * embT D τ r / (Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℂ)

def normConst (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : ℕ) (n : D.what₂.Tau → ℕ) : ℝ :=
  ∏ τ, (Real.pi / area (lamOf D cc δ)) ^ (a * n τ)

variable {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}

structure IsStdFrame (P : Pair D cc δ t0 Q) (Y : Frame P) : Prop where
  frame : IsFrame P Y
  ptA : ∀ x, GlobalTheory.BotFormula.IsFinPt Y.A (Y.ιA x) x
  ptB : ∀ h, GlobalTheory.BotFormula.IsFinPt Y.B (Y.ιB h) h

structure IsMaxLevel {P : Pair D cc δ t0 Q} (Y : Frame P) (K₀ : Subgroup (GL (Fin Y.B.rank) (Lev.EAf D)))
    (μ₀ : Measure (GA D Y.B)) : Prop where
  lev : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.B K₀
  mem_iff : ∀ h, Lev.finE Y.B (Y.ιB h) ∈ K₀ ↔ h ∈ intG D P.d
  meas : ∃ 𝓕, Links.IsMeasDef Y.B K₀ μ₀ 𝓕

structure IsExact (P : Pair D cc δ t0 Q) (X : Data P) (r : D.host.E) : Prop where
  std : IsStdFrame P X.toFrame
  inf : IsInfFam X.θ
  weil : IsWeilDatumO X.ψ X.A X.B X.χA X.χB X.om
  chA : HasFinPart X.χA P.W.chV P.W.ep
  chB : HasFinPart X.χB P.W.chV' (-P.W.ep')
  scale : IsScale D cc r
  read : Reads X.ψ X.θ X.rkA X.rkB cc δ r P.F X.vac
  const : X.c₁ = ∏ τ, period D δ r τ ^ (P.a * P.n τ)

theorem IsExact.setup {P : Pair D cc δ t0 Q} {X : Data P} {r : D.host.E} (h : IsExact P X r) :
    Setup X.ψ X.θ X.A X.B cc δ r :=
  ⟨h.weil.std, h.inf, h.std.frame.gramA, h.std.frame.gramB, P.crv, h.scale⟩

theorem isCongLevel_intG (N : ℕ) : IsCongLevel (intG D N) := ⟨1, one_pos, fun _ hk _ => hk⟩

theorem isScale_one (D : D7) : IsScale D D.host.ccK 1 := by simp [IsScale]

end GlobalTheory.NormExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExpansionIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest

namespace GlobalTheory.DepthUnf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def flatProd (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t)
    (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) : ℂ :=
  ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y)

def DepthOK (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (K : ℕ) : Prop :=
  (∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) → flatProd S t Φ β x y ≠ 0 →
        (∀ j : Fin D.R.m, K • x j ∈ pairLat G (.top t j)) ∧ ∀ i : Fin D.R.m, K • y i ∈ pairLat G (.chi i D.R.m)) ∧
  ∀ (x u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) → (∀ j : Fin D.R.m, IsHalf e (u j) ∧ u j ∈ pairLat G (.top t j)) →
      (∀ i : Fin D.R.m, IsHalf e (v i) ∧ v i ∈ pairLat G (.chi i D.R.m)) → flatProd S t Φ β (x + K • u) (y + K • v) = flatProd S t Φ β x y

def ExpWith (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) : Prop :=
  (∀ d ∈ τ.support, (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧
      ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1) ∧
    ∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) →
        (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) = flatProd S t Φ β x y

example (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) : DepthOK S t Φ β e 0 :=
  ⟨fun _ _ _ _ _ => ⟨fun _ => by rw [zero_smul]; exact zero_mem _, fun _ => by rw [zero_smul]; exact zero_mem _⟩,
    fun x u y v _ _ _ _ => by simp only [zero_smul, add_zero]⟩

end GlobalTheory.DepthUnf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfRationalExpansionsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRationalFormalPath_of_rationalExpansions : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (ξ : Sp (PowerSeries F) ⟶ Y), (∀ (U : Y.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ ξ ⁻¹ᵁ U) (f : Γ(Y, U)), IsRat (evAt ξ h f)) → IsRatPath ξ := by
  first | exact @GlobalTheory.Nef.isRatPath_of_isRat | exact GlobalTheory.Nef.isRatPath_of_isRat | (intros; apply GlobalTheory.Nef.isRatPath_of_isRat <;> assumption)
end

