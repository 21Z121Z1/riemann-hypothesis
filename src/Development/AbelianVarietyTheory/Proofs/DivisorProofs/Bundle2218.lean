import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFormsSpanInvariant
section
open NumberField

namespace GlobalTheory.IntFormsRank

variable {LL : Type} [Field LL] [NumberField LL] {n : ℕ}

theorem smul_eq_algebraMap_smul (r : 𝓞 LL) (z : Fin n → LL) : r • z = (algebraMap (𝓞 LL) LL r) • z :=
  (algebraMap_smul LL r z).symm

theorem exists_den_smul_mem (T : Set (Fin n → LL)) (x : Fin n → LL) (hx : x ∈ Submodule.span LL T) :
    ∃ d : 𝓞 LL, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 LL) T := by
  first
  | exact @_root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span
  | exact _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span
  | (apply _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span ..)

theorem span_inf_eq (T : Set (Fin n → LL)) (hT : Submodule.span LL T = ⊤) (S : Submodule LL (Fin n → LL)) :
    Submodule.span LL ((Submodule.span (𝓞 LL) T ⊓ S.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) (Fin n → LL)) :
      Set (Fin n → LL)) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro x hx
    have hxT : x ∈ Submodule.span LL T := by rw [hT]; exact Submodule.mem_top
    obtain ⟨d, hd, hdx⟩ := exists_den_smul_mem T x hxT
    have hdL : algebraMap (𝓞 LL) LL d ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 LL) LL)]; exact hd
    have hmem : d • x ∈ (Submodule.span (𝓞 LL) T ⊓ S.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) (Fin n → LL)) := by
      refine ⟨hdx, ?_⟩
      show d • x ∈ S
      rw [smul_eq_algebraMap_smul]; exact S.smul_mem _ hx
    have hx' : x = (algebraMap (𝓞 LL) LL d)⁻¹ • (d • x) := by
      rw [smul_eq_algebraMap_smul, smul_smul, inv_mul_cancel₀ hdL, one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.IntFormsRank

theorem GlobalTheory.IntFormsRank.rkK_Mall : ∀ (LL Ks : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] (n : ℕ)
    (Wσ : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    (G0 : Type) [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) (f : (Fin n → LL) →ₗ[LL] (Fin n → LL)),
    Submodule.span LL (A.MK : Set (Fin n → LL)) = ⊤ →
    Formalism.HN.rkK (A.Mall J0 lam0) = Module.finrank LL (A.typeP J0 lam0) ∧
    Formalism.HN.rkK (A.Mall J0 lam0 ⊓ (LinearMap.ker f).restrictScalars (𝓞 LL)) =
      Module.finrank LL (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)) := by
  intro LL Ks _ _ _ _ _ n Wσ _ _ G0 _ _ A J0 lam0 f hsp
  constructor
  · unfold Formalism.HN.rkK Formalism.IndefR.Arith.FormsL.Mall
    rw [GlobalTheory.IntFormsRank.span_inf_eq _ hsp]
  · unfold Formalism.HN.rkK Formalism.IndefR.Arith.FormsL.Mall
    have e : (Submodule.span (𝓞 LL) (A.MK : Set (Fin n → LL)) ⊓ (A.typeP J0 lam0).restrictScalars (𝓞 LL) ⊓
        (LinearMap.ker f).restrictScalars (𝓞 LL)) =
        Submodule.span (𝓞 LL) (A.MK : Set (Fin n → LL)) ⊓
          (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)).restrictScalars (𝓞 LL) := by
      rw [inf_assoc]; rfl
    rw [e, GlobalTheory.IntFormsRank.span_inf_eq _ hsp]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCompleteConnected
section
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem flat_injective_dvr {V O : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing O] [IsDomain O]
    (φ : V →+* O) (hφ : Function.Injective φ) : Flat (Spec.map (CommRingCat.ofHom φ)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  change φ.Flat
  algebraize [φ]
  change Module.Flat V O
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  rintro t ⟨⟨a, ha⟩, ht⟩
  have h1 : φ a * t = 0 := ht
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd (hφ (h.trans (map_zero φ).symm)) (nonZeroDivisors.ne_zero ha)
  · exact h

theorem connected_pullback_of_geomIrr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O) (hφ : Function.Injective φ)
    (_hloc : IsLocalHom φ) (X : Scheme.{0}) (s : X ⟶ Spec (.of V)) (Xw : X.Opens) (hX : IsIntegral X) (hs : Flat s)
    (hg : GeomIrr s Xw) : ConnectedSpace ↑(pullback s (Spec.map (CommRingCat.ofHom φ))) := by
  set K := FractionRing O
  set φ' := Spec.map (CommRingCat.ofHom φ)
  set ι' : Spec (.of K) ⟶ Spec (.of O) := Spec.map (CommRingCat.ofHom (algebraMap O K))
  set f : V →+* K := (algebraMap O K).comp φ
  have hf : Function.Injective f := (IsFractionRing.injective O K).comp hφ
  have hfe : spMap f = ι' ≫ φ' := by
    simp only [spMap, ι', φ', f, ← Spec.map_comp]
    rfl
  haveI hWi := hg K f hf
  set Wk := pullback (Xw.ι ≫ s) (spMap f)

  let m : Wk ⟶ pullback s φ' := pullback.lift (pullback.fst _ _ ≫ Xw.ι) (pullback.snd _ _ ≫ ι') (by
    simp only [Category.assoc]
    rw [← hfe]
    exact pullback.condition)
  haveI : Flat φ' := flat_injective_dvr φ hφ
  have gfst : GeneralizingMap (pullback.fst s φ') := by
    exact Flat.generalizingMap _
  have gsnd : GeneralizingMap (pullback.snd s φ') := by
    exact Flat.generalizingMap _

  haveI : IrreducibleSpace X := inferInstance
  set η := genericPoint X
  obtain ⟨w₀⟩ := (inferInstance : Nonempty Wk)
  have hη : η ∈ Xw := by
    exact ((genericPoint_spec X).mem_open_set_iff Xw.isOpen).2
      ⟨_, trivial, (pullback.fst (Xw.ι ≫ s) (spMap f) w₀).2⟩
  have key : ∀ x : ↥(pullback s φ'), x ∈ closure (Set.range m) := by
    intro x
    obtain ⟨x₁, hx₁, hx₁s⟩ := gsnd (b := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)) (a := x)
      ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le)
    obtain ⟨x₂, hx₂, hx₂f⟩ := gfst (genericPoint_specializes (pullback.fst s φ' x₁))
    have hs₂ : pullback.snd s φ' x₂ = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := by
      have := (hx₂.map (pullback.snd s φ').continuous)
      rw [hx₁s] at this
      exact PrimeSpectrum.ext (le_bot_iff.1 ((PrimeSpectrum.le_iff_specializes _ _).2 this))

    have hι : ι' (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := by
      have := bot_map (X := Spec (.of O)) (IsFractionRing.injective O K) (𝟙 _)
      exact this
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd s φ') (g := ι') x₂
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) (by rw [hs₂, hι])
    obtain ⟨y, hy₁, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := Xw.ι)
      (g := pullback.fst (pullback.snd s φ') ι' ≫ pullback.fst s φ') ⟨η, hη⟩ z
      (by rw [Scheme.Hom.comp_apply, hz₁, hx₂f]; rfl)
    let h : pullback Xw.ι (pullback.fst (pullback.snd s φ') ι' ≫ pullback.fst s φ') ⟶ Wk :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
        simp only [Category.assoc]
        rw [pullback.condition_assoc, Category.assoc, pullback.condition, pullback.condition_assoc, hfe])
    have hm : h ≫ m = pullback.snd _ _ ≫ pullback.fst (pullback.snd s φ') ι' := by
      apply pullback.hom_ext
      · simp only [Category.assoc, m, h, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [pullback.condition]
      · simp only [Category.assoc, m, h, pullback.lift_snd, pullback.lift_snd_assoc]
        rw [pullback.condition]
    have hx₂m : x₂ ∈ Set.range m := ⟨h y, by
      rw [← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply, hy₂, hz₁]⟩
    exact closure_mono (Set.singleton_subset_iff.2 hx₂m) (hx₂.trans hx₁).mem_closure
  have hirr : IsIrreducible (Set.range m) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ Wk).image _ m.continuous.continuousOn
  have : IrreducibleSpace ↑(pullback s φ') := by
    have hcl := hirr.closure
    rw [Set.eq_univ_of_forall key] at hcl
    exact (irreducibleSpace_def _).2 hcl
  infer_instance

end GlobalTheory.FlatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triangle_constant_exists : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ (r : ℂ) (rc : ℝ), r ≠ 0 ∧ (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) ∧ (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
          GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
          ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
              P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w))) := by
  first | exact @GlobalTheory.BotIntertw.bottom_intertwining | exact GlobalTheory.BotIntertw.bottom_intertwining | (intros; apply GlobalTheory.BotIntertw.bottom_intertwining <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundStatementHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel.BoundProof

section Gen

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem actV_mem_latT (a : Λ) {y : P.V} (hy : y ∈ P.latT) : P.actV a y ∈ P.latT :=
  (P.mem_latT_iff _).2 fun t => by
    obtain ⟨c, hc⟩ := (P.mem_latT_iff y).1 hy (P.actT (star a) t)
    exact ⟨c, by rw [hc, P.pairV_act]; rfl⟩

theorem pairV_inclT_mem {u : P.V} (hu : u ∈ P.latT) (y : O ⊗[ℤ_[p]] P.T) :
    P.pairV u (P.inclT y) ∈ (algebraMap O C).range := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add, map_add, map_add, ha, hb]⟩
  | tmul c t =>
    obtain ⟨b, hb⟩ := (P.mem_latT_iff u).1 hu t
    refine ⟨c * b, ?_⟩
    have e : (algebraMap O C c ⊗ₜ[ℤ_[p]] t : P.V) = algebraMap O C c • ((1 : C) ⊗ₜ[ℤ_[p]] t) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [P.inclT_tmul, e, map_smul, smul_eq_mul, map_mul, hb]

end Gen

section Gen2

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem pairV_bLie_inclT (x : LieG P.Gt) (y : O ⊗[ℤ_[p]] P.T) :
    P.pairV (P.bLie x) (P.inclT y) = algebraMap O C ((P.al y).1 x) := by
  rw [pairV_bLie_eq_evLie, P.alC_inclT, Point.inclOm, TensorProduct.mk_apply, evLie,
    LinearMap.liftBaseChange_tmul, one_smul]
  rfl

theorem exists_bLie_eq_sq_smul (hcok : ∀ f : omega P.Gt, (p : O) ^ 2 • f ∈ LinearMap.range P.al)
    (χ : Λ →+* O) {u : P.V} (hu : u ∈ P.latT) (hspan : u ∈ Submodule.span C (Set.range P.bLie))
    (heig : u ∈ P.eigV χ) :
    ∃ x : LieG P.Gt, AvDefs.IsEig P.Gt P.oGt χ x ∧ P.bLie x = ((p : C) ^ 2) • u := by
  haveI := P.isLocalRing
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  obtain ⟨e, h₁, h₂⟩ := exists_param P.G (smoothDim_model P)
  obtain ⟨e', h₃, h₄⟩ := exists_lieEquiv P
  let F := e.trans e'
  have hFadd : ∀ c d, F (c + d) = lieAdd (F c) (F d) := fun c d => Subtype.ext (h₃ _ _ _ (h₁ c d))
  have hFsmul : ∀ (a : O) c, F (a • c) = AvDefs.lieScale P.Gt a (F c) := fun a c =>
    Subtype.ext (h₄ a _ _ (h₂ a c))
  let B : (Fin P.A.g → O) →ₗ[O] P.V :=
    { toFun := fun c => P.bLie (F c)
      map_add' := fun c d => by rw [hFadd, P.bLie_add]
      map_smul' := fun a c => by rw [hFsmul, P.bLie_scale]; rfl }
  have hB : ∀ c, B c = P.bLie (F c) := fun _ => rfl
  let f : Fin P.A.g → omega P.Gt := fun j => ⟨fun x => F.symm x j, fun x y h => by
      have : (⟨x.1 * y.1, h⟩ : LieG P.Gt) = F (F.symm x + F.symm y) := by
        rw [hFadd, F.apply_symm_apply, F.apply_symm_apply]; rfl
      rw [this]; simp only [F.symm_apply_apply, Pi.add_apply], fun a x h => by
      have : (⟨ptMap (dualScale a) ≫ x.1, h⟩ : LieG P.Gt) = F (a • F.symm x) := by
        rw [hFsmul, F.apply_symm_apply]; rfl
      rw [this]; simp only [F.symm_apply_apply, Pi.smul_apply, smul_eq_mul]⟩
  have hf : ∀ j c, (f j).1 (F c) = c j := fun j c => by
    change F.symm (F c) j = c j
    rw [F.symm_apply_apply]
  choose y hy using fun j => hcok (f j)
  have hyF : ∀ j c, P.pairV (B c) (P.inclT (y j)) = algebraMap O C ((p : O) ^ 2 * c j) := fun j c => by
    rw [hB, pairV_bLie_inclT, hy j, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hf]
  have hp0 : ((p : O) ^ 2) ≠ 0 := pow_ne_zero _ fun h0 => (Nat.cast_ne_zero (R := C)).2
    (Fact.out : p.Prime).ne_zero (by rw [← map_natCast (algebraMap O C), h0, map_zero])
  have hBinj : ∀ c c', B c = B c' → c = c' := fun c c' hcc => funext fun j =>
    mul_left_cancel₀ hp0 (P.integers.hom_inj (by rw [← hyF, ← hyF, hcc]))
  have hinj : ∀ x x' : LieG P.Gt, P.bLie x = P.bLie x' → x = x' := fun x x' hxx => by
    rw [← F.apply_symm_apply x, ← F.apply_symm_apply x'] at hxx ⊢
    exact congrArg F (hBinj _ _ hxx)
  let s : Fin P.A.g → P.V := fun i => B fun j => if i = j then 1 else 0
  have hBs : ∀ c, B c = ∑ i, c i • s i := fun c => B.pi_apply_eq_sum_univ c
  have hspan' : u ∈ Submodule.span C (Set.range s) := by
    refine Submodule.span_le.2 ?_ hspan
    rintro _ ⟨x, rfl⟩
    rw [← F.apply_symm_apply x, ← hB, hBs]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul C]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hspan'
  have hint : ∀ j, ((p : C) ^ 2 * a j) ∈ (algebraMap O C).range := fun j => by
    have h := pairV_inclT_mem P hu (y j)
    rw [← ha] at h
    convert h using 1
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [hyF]
      simp [map_pow, map_natCast, mul_comm]
    · intro i _ hij
      rw [hyF]
      simp [hij, Ne.symm hij]
    · simp
  choose b hb using hint
  have hx : P.bLie (F b) = ((p : C) ^ 2) • u := by
    rw [← hB, hBs, ← ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul C (b i), hb, smul_smul]
  refine ⟨F b, fun c => hinj _ _ ?_, hx⟩
  rw [P.bLie_act, P.bLie_scale, hx, map_smul, mem_eigenSub.1 heig c, RingHom.comp_apply,
    ← algebraMap_smul C (χ c) ((p : C) ^ 2 • u), smul_smul, smul_smul, mul_comm]

end Gen2

section Discr

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E))

theorem discr_smul_proj_mem {_ : DecidableEq (E →+* C)} (i : E →+* C) {y : P.V} (hy : y ∈ P.latT) :
    ((discr E : ℤ) : C) • proj (isSplitting_embO (E := E) P.integers) P.actV i y ∈ P.latT := by
  classical
  have hc : Fintype.card (E →+* C) = Module.finrank ℚ E := NumberField.Embeddings.card E C
  obtain ⟨b⟩ := nonempty_basis (E := E) hc
  let M : Matrix (E →+* C) (E →+* C) O := Matrix.of fun k j => embO P.integers k (b j)
  have hM : M.map (algebraMap O C) = Matrix.of fun k j => k (b j) := by
    ext k j
    simp [M, algebraMap_embO]
  have hd : algebraMap O C M.det ^ 2 = ((discr E : ℤ) : C) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact det_sq_eq_discr_of_field (φ := fun φ : E →+* C => φ) (fun _ _ h => h) b
  let o : (E →+* C) → O := fun j => M.det * M.adjugate j i
  let t : C ⊗[ℤ] 𝓞 E := ∑ j, algebraMap O C (o j) ⊗ₜ b j
  have ht : t = ((discr E : ℤ) : C) • idem (isSplitting_embO (E := E) P.integers) i := by
    apply (isSplitting_embO (E := E) P.integers).1
    rw [map_smul, splitMap_idem]
    ext k
    simp only [t, map_sum, Finset.sum_apply, splitMap_tmul, RingHom.comp_apply, Pi.smul_apply, smul_eq_mul]
    have e1 : ∑ j, algebraMap O C (o j) * algebraMap O C (embO P.integers k (b j)) =
        algebraMap O C (M.det * (M * M.adjugate) k i) := by
      rw [Matrix.mul_apply, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [o, M, Matrix.of_apply, map_mul]
      ring
    rw [e1, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, ← hd]
    by_cases hki : k = i
    · subst hki; simp [sq]
    · simp [hki]
  have e2 : ((discr E : ℤ) : C) • proj (isSplitting_embO (E := E) P.integers) P.actV i y =
      tensorAction P.actV t y := by
    rw [ht, map_smul, proj, LinearMap.smul_apply]
  rw [e2]
  simp only [t, map_sum, LinearMap.sum_apply, tensorAction_tmul]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ _ (actV_mem_latT P _ hy)

end Discr

theorem discr_smul_mem_latT {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) {p : ℕ} [Fact p.Prime] [Algebra c.F ℂ_[p]] [StarRing (𝓞 E)] (P : PtP E p)
    (σ : E →+* ℂ) {w : P.V} (hw : w ∈ htLat c P σ) : ((discr E : ℤ) : ℂ_[p]) • w ∈ P.latT := by
  unfold htLat at hw
  split_ifs at hw with h
  · obtain ⟨y, hy, rfl⟩ := hw
    exact discr_smul_proj_mem P _ hy
  · rw [Int.cast_smul_eq_zsmul]
    exact zsmul_mem hw.1 _

end GlobalTheory.FlatModel.BoundProof

namespace GlobalTheory.FlatModel

theorem boundSt : BoundSt := by
  intro E _ _ _ H l c p _ _ _ P hcok σ w hw hspan heig
  obtain ⟨x, hx, hbx⟩ := BoundProof.exists_bLie_eq_sq_smul P hcok (embInt c P.integers σ)
    (BoundProof.discr_smul_mem_latT c P σ hw) (Submodule.smul_mem _ _ hspan) (Submodule.smul_mem _ _ heig)
  exact ⟨x, hx, by rw [hbx, smul_smul, mul_comm]⟩

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedPowerSeriesEvaluationDivisibility
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.BddPS

def bdd (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] : Subring (PowerSeries C) :=
  GlobalTheory.BoundedPowerSeriesDisc.boundedSeries C

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

noncomputable def ev [CompleteSpace C] (π : C) (h : ‖π‖ < 1) : bdd C →+* C :=
  GlobalTheory.BoundedPowerSeriesDisc.evalBounded π h

theorem main : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (π : C), ‖π‖ < 1 → ∃ (B : Subring (PowerSeries C)) (ev : B →+* C) (t : B), (∀ Φ, Φ ∈ B ↔ ∃ b : ℝ, ∀ n, ‖PowerSeries.coeff n Φ‖ ≤ b) ∧ (∀ Φ : B, ev Φ = ∑' n, PowerSeries.coeff n (Φ : PowerSeries C) * π ^ n) ∧ t ≠ 0 ∧ (∀ Φ, ev Φ = 0 ↔ t ∣ Φ) ∧ ∀ Φ : B, Φ ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ Φ := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.SummableSeriesBounds.main
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.SummableSeriesBounds.main
  | exact @_root_.GlobalTheory.SummableSeriesBounds.main
  | exact _root_.GlobalTheory.SummableSeriesBounds.main
  | (apply _root_.GlobalTheory.SummableSeriesBounds.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SummableSeriesBounds.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SummableSeriesBounds.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SummableSeriesBounds.main ..)

end GlobalTheory.MBLow.BddPS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassCartierDivisorPullbackEqPullback
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.PullCartier

theorem fnOf_app {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    {U : W.Opens} (h : genericPoint M ∈ f ⁻¹ᵁ U) (a : Γ(W, U)) :
    fnOf (f ⁻¹ᵁ U) h ((f.app U).hom a) =
      GlobalTheory.functionFieldMap f (fnOf U (gen_mem (x := f (genericPoint M)) h) a) := by
  have hx : f (genericPoint M) ∈ U := h
  rw [← algebraMap_germ hx a, GlobalTheory.functionFieldMap_algebraMap, Scheme.Hom.germ_stalkMap_apply f U _ hx a]
  exact (algebraMap_germ (X := M) (U := f ⁻¹ᵁ U) (x := genericPoint M) h _).symm

theorem cls_toLB_pull : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    (D₀ : CartierDiv W) (D₁ : CartierDiv M),
    (∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g)) →
      cls (toLB D₁) (isLB_toLB D₁) = CechPic.pull f (cls (toLB D₀) (isLB_toLB D₀)) := by
  intro M W _ _ f _ D₀ D₁ hD
  have hP : Presents D₁ ((toLB D₀).pull f)
      fun J => Units.map (GlobalTheory.functionFieldMap f).toMonoidHom (J PUnit.unit).1.2 := by
    refine ⟨pull_isLB (isLB_toLB D₀) f, fun J K h => ?_,
      fun J x hx => hD x _ ((J PUnit.unit).2.2 _ (mem_pull.1 hx))⟩
    have hle : ((toLB D₀).pull f).U J ⊓ ((toLB D₀).pull f).U K ≤
        f ⁻¹ᵁ ((toLB D₀).U (J PUnit.unit) ⊓ (toLB D₀).U (K PUnit.unit)) :=
      fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
    have e0 : ((toLB D₀).pull f).g J K =
        res hle (pullU f _ ((toLB D₀).g (J PUnit.unit) (K PUnit.unit))) :=
      by dsimp only [LB.pull, LB.LinComb]; rw [Fintype.prod_unique, zpow_one]; rfl
    have e : fnOf _ h (((toLB D₀).pull f).g J K).val =
        fnOf _ (hle h) ((f.app _).hom ((toLB D₀).g (J PUnit.unit) (K PUnit.unit)).val) := by
      rw [e0, LB.val_res, fnOf_resG]
      rfl
    rw [e, fnOf_app, fnOf_toLB_g]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    rw [← map_mul, div_mul_cancel₀ _ (Units.ne_zero _)]
  rw [← cls_pull (isLB_toLB D₀) f hP.isLB, ← toPic_apply, hP.toPic_eq]

end GlobalTheory.PullCartier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroStalkCompactFlagSpaceOverComponent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.CompHS

theorem charZero_stalk_Y₀ : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (y : Y₀ TF.X Z), CharZero ((Y₀ TF.X Z).presheaf.stalk y) := by
  intro E _ _ _ H Dw l Xo c TF Z y
  let f : c.F →+* (Y₀ TF.X Z).presheaf.stalk y :=
    ((Y₀ TF.X Z).presheaf.germ ⊤ y trivial).hom.comp
      ((str₀ TF.X Z).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom)
  exact charZero_of_injective_ringHom f.injective

end GlobalTheory.CompHS
end

