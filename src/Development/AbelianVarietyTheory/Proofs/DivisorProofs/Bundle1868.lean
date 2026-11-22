import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1837
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0150
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0125
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NullOfFiniteCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceTransformSchwartzBijective
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapSliceBij

open GlobalTheory.SwapSlice

theorem totDisc_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : TotallyDisconnectedSpace k := by
  haveI : T2Space k := inferInstance
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  infer_instance

theorem conj_mem_SB {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf : f ∈ SB X) :
    (fun x => starRingEnd ℂ (f x)) ∈ SB X :=
  ⟨hf.1.comp (starRingEnd ℂ), hf.2.comp_left (map_zero _)⟩

theorem barL_bijOn {k Y : Type} [TopologicalSpace k] [TopologicalSpace Y] {κ : Type}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (h : Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB Y : Set (Y → ℂ))) :
    Set.BijOn (barL ι) (SB (κ → k) : Set ((κ → k) → ℂ)) (SB Y : Set (Y → ℂ)) := by
  refine ⟨fun φ hφ => conj_mem_SB (h.mapsTo (conj_mem_SB hφ)), fun φ hφ ψ hψ e => ?_, fun g hg => ?_⟩
  · have e' : ι (fun x => starRingEnd ℂ (φ x)) = ι (fun x => starRingEnd ℂ (ψ x)) := by
      funext y
      have := congrFun e y
      simp only [barL_apply] at this
      simpa using congrArg (starRingEnd ℂ) this
    have e'' := h.injOn (conj_mem_SB hφ) (conj_mem_SB hψ) e'
    funext x
    simpa using congrArg (starRingEnd ℂ) (congrFun e'' x)
  · obtain ⟨φ', hφ', e⟩ := h.surjOn (conj_mem_SB hg)
    refine ⟨fun x => starRingEnd ℂ (φ' x), conj_mem_SB hφ', ?_⟩
    funext y
    simp [barL_apply, e]

theorem boxFun_mem {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

variable {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] [LocallyCompactSpace k] [TotallyDisconnectedSpace k]
  {κ : Type} [Fintype κ]

theorem SB_le_span_boxFun :
    SB (κ ⊕ κ → k) ≤ Submodule.span ℂ {f | ∃ φ₁ ∈ SB (κ → k), ∃ φ₂ ∈ SB (κ → k), f = boxFun φ₁ φ₂} := by
  intro Φ hΦ
  let e := Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ)
  have hspan := GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (κ → k) (κ → k)
  let T : GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) →ₗ[ℂ] ((κ ⊕ κ → k) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ e) ∘ₗ (GlobalTheory.SplitWeil.SB _).subtype
  have hΦ' : Φ ∘ e.symm ∈ GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) :=
    ⟨hΦ.1.comp_continuous e.symm.continuous, hΦ.2.comp_homeomorph e.symm⟩
  have key : Φ ∈ Submodule.map T ⊤ := ⟨⟨Φ ∘ e.symm, hΦ'⟩, trivial, by
    funext x; simp [T, LinearMap.funLeft]⟩
  rw [← hspan, Submodule.map_span, ← Set.range_comp] at key
  refine Submodule.span_mono ?_ key
  rintro _ ⟨q, rfl⟩
  exact ⟨q.1.1, q.1.2, q.2.1, q.2.2, by funext x; rfl⟩

theorem mem_of_boxFun {M : Type} [AddCommGroup M] [Module ℂ M] (L : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] M) (P : Submodule ℂ M)
    (h : ∀ φ₁ ∈ SB (κ → k), ∀ φ₂ ∈ SB (κ → k), L (boxFun φ₁ φ₂) ∈ P) : ∀ Φ ∈ SB (κ ⊕ κ → k), L Φ ∈ P := by
  intro Φ hΦ
  have hle : Submodule.span ℂ {f | ∃ φ₁ ∈ SB (κ → k), ∃ φ₂ ∈ SB (κ → k), f = boxFun φ₁ φ₂} ≤ P.comap L :=
    Submodule.span_le.2 (by rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩; exact h φ₁ h₁ φ₂ h₂)
  exact hle (SB_le_span_boxFun hΦ)

end GlobalTheory.SwapSliceBij

open GlobalTheory.SwapSlice GlobalTheory.SwapSliceBij in

theorem GlobalTheory.SwapSliceBij.sliceT_bijOn : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {κ : Type} [Fintype κ] {n d : ℕ}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB (Matrix (Fin n) (Fin d) k) : Set _) →
    Set.BijOn (GlobalTheory.SwapSlice.sliceT ι) (SB (κ ⊕ κ → k) : Set ((κ ⊕ κ → k) → ℂ))
      (SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k) : Set _) := by
  intro k _ _ _ _ κ _ n d ι hι
  haveI : T2Space k := inferInstance
  haveI := totDisc_localField k
  haveI : LocallyCompactSpace k := inferInstance
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → k))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → k))
  haveI : T2Space (Matrix (Fin n) (Fin d) k) := inferInstanceAs (T2Space (Fin n → Fin d → k))
  have hbar := barL_bijOn ι hι

  have hslice : ∀ x₂ : κ → k, ∀ Φ ∈ SB (κ ⊕ κ → k), (fun x₁ => Φ (Sum.elim x₁ x₂)) ∈ SB (κ → k) := by
    intro x₂
    refine mem_of_boxFun (LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (SB (κ → k)) ?_
    intro φ₁ h₁ φ₂ h₂
    have e : LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂) (boxFun φ₁ φ₂) = φ₂ x₂ • φ₁ := by
      funext x₁; simp [LinearMap.funLeft, boxFun, Function.comp_def, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ h₁

  have hcol : ∀ Z₁ : Matrix (Fin n) (Fin d) k, ∀ Φ ∈ SB (κ ⊕ κ → k),
      (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z₁) ∈ SB (κ → k) := by
    intro Z₁
    refine mem_of_boxFun (LinearMap.pi fun x₂ : κ → k => (LinearMap.proj Z₁) ∘ₗ ι ∘ₗ
      LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (SB (κ → k)) ?_
    intro φ₁ h₁ φ₂ h₂
    have e : (LinearMap.pi fun x₂ : κ → k => (LinearMap.proj Z₁) ∘ₗ ι ∘ₗ
        LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (boxFun φ₁ φ₂) = ι φ₁ Z₁ • φ₂ := by
      funext x₂
      have e' : LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂) (boxFun φ₁ φ₂) = φ₂ x₂ • φ₁ := by
        funext x₁; simp [LinearMap.funLeft, boxFun, Function.comp_def, mul_comm]
      simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, e', map_smul, LinearMap.coe_proj,
        Function.eval, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]; exact Submodule.smul_mem _ _ h₂
  have hz : ∀ Φ ∈ SB (κ ⊕ κ → k), sliceT ι Φ = 0 → Φ = 0 := by
    intro Φ hΦ h0
    have h1 : ∀ Z₁, (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z₁) = 0 := by
      intro Z₁
      refine hbar.injOn (hcol Z₁ Φ hΦ) (zero_mem _) ?_
      rw [map_zero]; funext Z₂; exact congrFun h0 (Z₁, Z₂)
    have h2 : ∀ x₂, (fun x₁ => Φ (Sum.elim x₁ x₂)) = 0 := by
      intro x₂
      refine hι.injOn (hslice x₂ Φ hΦ) (zero_mem _) ?_
      rw [map_zero]; funext Z₁; exact congrFun (h1 Z₁) x₂
    funext x
    have := congrFun (h2 (x ∘ Sum.inr)) (x ∘ Sum.inl)
    simpa [Sum.elim_comp_inl_inr] using this
  refine ⟨?_, fun Φ hΦ Ψ hΨ e => sub_eq_zero.1 (hz (Φ - Ψ) (sub_mem hΦ hΨ) (by rw [map_sub, e, sub_self])), ?_⟩
  · intro Φ hΦ
    refine mem_of_boxFun (sliceT ι) _ ?_ Φ hΦ
    intro φ₁ h₁ φ₂ h₂
    have e : sliceT ι (boxFun φ₁ φ₂) = GlobalTheory.LocFlat.CFac.prodFn (ι φ₁) (barL ι φ₂) := by
      funext Z; rw [sliceT_boxFun]; rfl
    rw [e]; exact GlobalTheory.LocFlat.CFac.prodFn_mem_SB (hι.mapsTo h₁) (hbar.mapsTo h₂)
  · intro g hg
    have hspan := GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (Matrix (Fin n) (Fin d) k) (Matrix (Fin n) (Fin d) k)
    have key : g ∈ Submodule.map (GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k)).subtype ⊤ :=
      ⟨⟨g, hg⟩, trivial, rfl⟩
    rw [← hspan, Submodule.map_span, ← Set.range_comp] at key
    have hle : Submodule.span ℂ (Set.range ((GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k)).subtype ∘
        fun q : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) × GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) =>
          GlobalTheory.LocFlat.CFac.prodSB q.1 q.2)) ≤ Submodule.map (sliceT ι) (SB (κ ⊕ κ → k)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨q, rfl⟩
      obtain ⟨φ₁, h₁, e₁⟩ := hι.surjOn q.1.2
      obtain ⟨φ₂, h₂, e₂⟩ := hbar.surjOn q.2.2
      refine ⟨boxFun φ₁ φ₂, boxFun_mem h₁ h₂, ?_⟩
      funext Z
      rw [sliceT_boxFun, e₁, e₂]
      rfl
    obtain ⟨Φ, hΦ, e⟩ := Submodule.mem_map.1 (hle key)
    exact ⟨Φ, hΦ, e⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemScLatOfMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat

theorem smul_mem_scLat_of_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    {Λ : Submodule (𝓞 E) (Fin n → E)} {a : E} (ha : a ∈ 𝔞) {y : Fin n → E} (hy : y ∈ Λ) :
    a • y ∈ GlobalTheory.SkewLat.scLat 𝔞 Λ := by
  intro c hc
  have h : a * c ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
    FractionalIdeal.mul_one_div_le_one (FractionalIdeal.mul_mem_mul ha hc)
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h
  rw [smul_smul, mul_comm, ← hr, algebraMap_smul]
  exact Λ.smul_mem r hy

theorem divG_gen {D : D7} (S : HSp D) {n : ℕ} (β : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin n → D.host.E) (p : Fin n) (q : Fin S.rank) :
    divG S (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) p q =
      β ⊗ₜ[D.host.F] (a * t p * star (s q)) := by
  have h : (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : Matrix _ _ (AE D)) =
      mulG S (Matrix.of fun i k => β ⊗ₜ[D.host.F] (a * t i * star (s k))) := by
    ext i j
    rw [mulG_eq, Matrix.mul_apply]
    simp only [of_apply, map_apply, Finset.mul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ = (β ⊗ₜ[D.host.F] (a * t i * star (s k))) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram k j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc (a * t i)]
  rw [h, divG_mulG, of_apply]

theorem divG_zero {D : D7} (S : HSp D) {n : ℕ} : divG S (0 : Matrix (Fin n) (Fin S.rank) (AE D)) = 0 :=
  Matrix.zero_mul _

theorem divG_neg {D : D7} (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : divG S (-x) = -divG S x :=
  Matrix.neg_mul _ _

theorem smul_incM_apply {D : D7} {m n : Type} (β : AF D.host.F) (M : Matrix m n D.host.E) (p : m) (q : n) :
    (β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F M) p q = β ⊗ₜ[D.host.F] M p q := by
  change β • ((1 : AF D.host.F) ⊗ₜ[D.host.F] M p q) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem one_smul_gen_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {α : Af F} (hα : α ∈ intAf F) {x : Fin n → E} (hx : x ∈ X.L)
    {y : Fin d → E} (hy : y ∈ Y.L) :
    GlobalTheory.LatVac.liftV v 1 • pairA F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (vecMulVec x y) ∈ latAtV X Y v := by
  rw [smul_smul]
  refine AddSubgroup.subset_closure ⟨_, ?_, ?_, x, hx, y, hy, rfl⟩
  · intro u hu
    rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u, GlobalTheory.LatVac.at_liftV v 1 u hu, zero_mul]
  · rw [map_mul, GlobalTheory.LatVac.evFin_liftV, one_mul]
    exact hα v

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem ofMaps_inl (e : Num G i j) (x : HomV G i j × HomW G i j) (p : Fin (spW G i j).rank) (k : Fin (spV G i j).rank) :
    ofMaps e x p (e (.inl k)) = divG (negSp (spW G i j)) x.1 k p := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]

theorem ofMaps_inr (e : Num G i j) (x : HomV G i j × HomW G i j) (p : Fin (spW G i j).rank) (k : Fin (spV₁ G i j).rank) :
    ofMaps e x p (e (.inr k)) = cA D (divG (spV₁ G i j) (-x.2) p k) := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]

theorem ofMaps_genV (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spW G i j).rank → D.host.E)
    (t : Fin (spV G i j).rank → D.host.E) :
    ofMaps e (Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * t i' * ∑ k, star (s k) * (negSp (spW G i j)).gram k j'), 0) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (Sum.elim (a • t) 0 ∘ e.symm)) := by
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inl e _ p k).trans ((divG_gen (negSp (spW G i j)) β a s t k p).trans ?_)
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, mul_comm]
    rfl
  · refine (ofMaps_inr e _ p k).trans ?_
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, neg_zero, divG_zero,
      Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    exact map_zero _

theorem ofMaps_genW (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spV₁ G i j).rank → D.host.E)
    (t : Fin (spW G i j).rank → D.host.E) :
    ofMaps e (0, Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * t i' * ∑ k, star (s k) * (spV₁ G i j).gram k j')) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star (-t)) (Sum.elim 0 (star (a • star s)) ∘ e.symm)) := by
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inl e _ p k).trans ((congrFun (congrFun (divG_zero (negSp (spW G i j))) k) p).trans ?_)
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl,
      Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    rfl
  · refine (ofMaps_inr e _ p k).trans ?_
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, divG_neg, Matrix.neg_apply,
      divG_gen, ← TensorProduct.tmul_neg]
    change β ⊗ₜ[D.host.F] star (-(a * t p * star (s k))) = β ⊗ₜ[D.host.F] (star (-t p) * star (a * star (s k)))
    rw [← star_mul']
    congr 2
    ring

theorem map_mem_of_closure {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) {s : Set A} {H : AddSubgroup B}
    (h : ∀ x ∈ s, f x ∈ H) {x : A} (hx : x ∈ AddSubgroup.closure s) : f x ∈ H :=
  (AddSubgroup.closure_le (H.comap f)).2 h hx

theorem pair_mem {E : Type} [Field E] [NumberField E] {a b d : ℕ} {ΛA : Submodule (𝓞 E) (Fin a → E)}
    {ΛB : Submodule (𝓞 E) (Fin b → E)} (e : Fin a ⊕ Fin b ≃ Fin d) {x : Fin a → E} {y : Fin b → E} (hx : x ∈ ΛA) (hy : y ∈ ΛB) :
    Sum.elim x y ∘ e.symm ∈ GlobalTheory.SkewLat.pairLat ΛA ΛB e := by
  rw [GlobalTheory.SkewLat.mem_pairLat]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  exact ⟨hx, hy⟩

theorem star_mem_conjSub {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)}
    {y : Fin n → E} (hy : y ∈ Λ) : star y ∈ GlobalTheory.TripleSpaceW.conjSub Λ := by
  rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hy

theorem smul_ofMaps_inl_mem {t : T} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} (h : IsTied t i j e Bs Γ X) (v : Pl D.host.F) {x : HomV G i j} (hx : x ∈ latV G i j) :
    GlobalTheory.LatVac.liftV v 1 • ofMaps e (x, 0) ∈ latAtV Γ.V Γ.W v := by
  refine map_mem_of_closure ((DistribMulAction.toAddMonoidHom (Pt G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inl _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V Γ.W v) (ofMaps_genV e (pairA _ 0 α) a s t)).mpr
    (one_smul_gen_mem _ _ v hα (h.1.ge (star_mem_conjSub hs))
      (h.2.1.ge (pair_mem e (smul_mem_scLat_of_mem ha ht) (zero_mem _))))

theorem smul_ofMaps_inr_mem {t : T} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} (h : IsTied t i j e Bs Γ X) (v : Pl D.host.F) {x : HomW G i j} (hx : x ∈ latW G i j) :
    GlobalTheory.LatVac.liftV v 1 • ofMaps e (0, x) ∈ latAtV Γ.V Γ.W v := by
  refine map_mem_of_closure ((DistribMulAction.toAddMonoidHom (Pt G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inr _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V Γ.W v) (ofMaps_genW e (pairA _ 0 α) a s t)).mpr
    (one_smul_gen_mem _ _ v hα (h.1.ge (star_mem_conjSub (neg_mem ht)))
      (h.2.1.ge (pair_mem e (zero_mem _) (star_mem_conjSub (smul_mem_scLat_of_mem ha (star_mem_conjSub hs))))))

theorem latPt_le_latAtV : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (i j : ℕ) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E), IsTied t i j e Bs Γ X →
    ∀ v : Pl D.host.F, ∀ u ∈ latPt e v, u ∈ latAtV Γ.V Γ.W v := by
  intro D T L sc G t i j e Bs Γ X h v u hu
  obtain ⟨hat, h1, h2⟩ := hu
  have e1 : GlobalTheory.LatVac.liftV v 1 • u = u := by
    have := hat (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have e2 : u = ofMaps e (mapV e u, 0) + ofMaps e (0, mapW e u) :=
    ((ofMaps_maps e u).symm.trans (congrArg (ofMaps e) (Prod.ext (add_zero _).symm (zero_add _).symm))).trans
      (map_add (maps e).symm (mapV e u, 0) (0, mapW e u))
  have e3 := add_mem (smul_ofMaps_inl_mem h v h1) (smul_ofMaps_inr_mem h v h2)
  rwa [← smul_add, ← e2, e1] at e3

end GlobalTheory.BigDat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomPairsWeightsEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareBottomPairs_weights_eq : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T) (i j : Fin D.R.m)
    (𝔪 : Ideal (𝓞 D.host.E)) {δ t0 : ℂ} {Q : ℕ} (P P' : Pair D ⊤ δ t0 Q), IsBottom G t i j 𝔪 P P' → P'.n = P.n := by
  first | exact @GlobalTheory.BottomWeights.isBottom_n_eq | exact GlobalTheory.BottomWeights.isBottom_n_eq | (intros; apply GlobalTheory.BottomWeights.isBottom_n_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStepCharIdealValueEqBaseMulRootOfUnity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.SqStepIdeal

open GlobalTheory.LFun

theorem val_mem {D : D7} {χ : HChar D.host.E} {n : ℕ} (h1 : χ.OrderDvd n) (h2 : LocIn D.what₂.embLL χ)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) :
    χ.val w ^ n = 1 ∧ ((χ.val w : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  refine ⟨?_, ?_⟩
  · have e1 : (χ.1 : _ →* ℂˣ) ^ n = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    have e2 : ∀ y, χ.1 y ^ n = 1 := fun y => by
      have := DFunLike.congr_fun e1 y
      simpa [MonoidHom.pow_apply] using this
    exact e2 _
  · obtain ⟨y, hy⟩ := h2 w (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))
    exact ⟨y, hy⟩

theorem mulSupport_finite {E : Type} [Field E] [NumberField E] (f : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → ℂˣ)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    (Function.mulSupport fun w => f w ^ FractionalIdeal.count E w 𝔞).Finite := by
  refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors 𝔞)).subset fun w hw => ?_
  intro h
  apply hw
  simp only [h, zpow_zero]

theorem idealVal_chs_base : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), ∃ b : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ b ^ n = 1) ∧
      ((idealVal (GlobalTheory.SqStep.chs G i j μ₀).ν 𝔞 : ℂˣ) : ℂ) = D.what₂.embLL b * ((idealVal (GlobalTheory.SqStep.chs G i j t).ν 𝔞 : ℂˣ) : ℂ) := by
  intro D T Lc sc G μ₀ hL W S hN i j t 𝔞
  have e : ∀ s, (GlobalTheory.SqStep.chs G i j s).ν = G.nu s i (j + 1) := fun s => by
    show (Lc.mu s (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  have hν : (GlobalTheory.SqStep.chs G i j μ₀).ν = (GlobalTheory.SqStep.chs G i j t).ν * ((Lc.xi t)⁻¹ * Lc.xi μ₀) := by
    rw [e, e]
    refine MonoidHom.ext fun x => ?_
    show Lc.mu0 (j + 1) x * Lc.xi μ₀ x / G.ch.chi (D.R.m - i) x =
      Lc.mu0 (j + 1) x * Lc.xi t x / G.ch.chi (D.R.m - i) x * ((Lc.xi t x)⁻¹ * Lc.xi μ₀ x)
    rw [div_mul_eq_mul_div, mul_assoc (Lc.mu0 (j + 1) x) (Lc.xi t x), mul_inv_cancel_left]
  obtain ⟨n, hn, hfin⟩ := hL.xi_fin t
  let c : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := fun w => ((Lc.xiH t).val w)⁻¹
  have hw : ∀ w, val (GlobalTheory.SqStep.chs G i j μ₀).ν w = val (GlobalTheory.SqStep.chs G i j t).ν w * c w := fun w => by
    rw [hν, val_mul, val_mul, val_inv, val_eq_of_chrEq (hL.xi t) w, val_eq_of_chrEq (hL.xi μ₀) w, hL.xi_base]
    rw [show (1 : HChar D.host.E).val w = 1 from rfl, mul_one]
  let H : Subgroup ℂˣ :=
    { carrier := {z | z ^ n = 1 ∧ (z : ℂ) ∈ D.what₂.embLL.fieldRange}
      mul_mem' := fun ha hb => ⟨by rw [mul_pow, ha.1, hb.1, one_mul], by rw [Units.val_mul]; exact mul_mem ha.2 hb.2⟩
      one_mem' := ⟨one_pow _, by rw [Units.val_one]; exact one_mem _⟩
      inv_mem' := fun ha => ⟨by rw [inv_pow, ha.1, inv_one], by rw [Units.val_inv_eq_inv_val]; exact inv_mem ha.2⟩ }
  have hc : ∀ w, c w ∈ H := fun w => H.inv_mem (val_mem hfin (hN.chars.xi t) w)
  have hprod : idealVal (GlobalTheory.SqStep.chs G i j μ₀).ν 𝔞 =
      idealVal (GlobalTheory.SqStep.chs G i j t).ν 𝔞 * ∏ᶠ w, c w ^ FractionalIdeal.count D.host.E w 𝔞 := by
    unfold idealVal
    simp_rw [hw, mul_zpow]
    exact finprod_mul_distrib (mulSupport_finite _ 𝔞) (mulSupport_finite _ 𝔞)
  have hz : ∏ᶠ w, c w ^ FractionalIdeal.count D.host.E w 𝔞 ∈ H := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := (mulSupport_finite c 𝔞).toFinset) (by simp)]
    exact H.prod_mem fun w _ => H.zpow_mem (hc w) _
  obtain ⟨hzn, hzr⟩ := hz
  obtain ⟨b, hb⟩ := RingHom.mem_fieldRange.1 hzr
  refine ⟨b, ⟨n, hn, ?_⟩, ?_⟩
  · apply D.what₂.embLL.injective
    rw [map_pow, hb, map_one, ← Units.val_pow_eq_pow_val, hzn, Units.val_one]
  · rw [hprod, Units.val_mul, hb, mul_comm]

end GlobalTheory.SqStepIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strongApproximation_splitPlace_skewHermitian_unitary : GlobalTheory.Published.StrongApproxSU → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ (v : Bs.P) (s : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J), (mat s).det = 1 →
      s ∈ closure {x | ∃ γ ∈ ratU σ Γ.W.J, ∃ k ∈ UAt σ Γ.W (evFin F v.1), x = γ * k} := by
  first | exact @GlobalTheory.SplitApprox.strongApprox_split | exact GlobalTheory.SplitApprox.strongApprox_split | (intros; apply GlobalTheory.SplitApprox.strongApprox_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaAdelicHaarEqMapProductMeasureStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tamagawa_adelicHaar_eq_map_product_measure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (e : κ ≃ Fin N) (ν : Measure (AF F)), GlobalTheory.SWQ.IsCov1 ν → ∀ μ : Measure (κ → AF F), IsTamagawa F κ μ → μ = Measure.map (GlobalTheory.PoissonReindex.reidx (F := F) e) (GlobalTheory.SWQ.muV N ν) := by
  first | exact @GlobalTheory.SWLit.tamagawa_eq_map_pi | exact GlobalTheory.SWLit.tamagawa_eq_map_pi | (intros; apply GlobalTheory.SWLit.tamagawa_eq_map_pi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfIntegralTraceStatement
section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_le_one_of_integral_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → ∀ c : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * c))) → w.valuation E c ≤ 1 := by
  first | exact @GlobalTheory.CodiffValPrimeW.valuation_le_one_of_mem_codiff | exact GlobalTheory.CodiffValPrimeW.valuation_le_one_of_mem_codiff | (intros; apply GlobalTheory.CodiffValPrimeW.valuation_le_one_of_mem_codiff <;> assumption)
end

