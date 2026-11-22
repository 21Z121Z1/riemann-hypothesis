import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleStageOfPackage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0569
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsLogGrNormSubLe
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.HTFrame

attribute [local instance] Over.cartesianMonoidalCategory

theorem abs_log_sInf_sub_le {A B : Set ℝ} {c : ℝ} (hc : 1 ≤ c) (hB : ∀ r ∈ B, 0 ≤ r) (hAB : A ⊆ B)
    (hBA : ∀ r ∈ B, c * r ∈ A) : |Real.log (sInf A) - Real.log (sInf B)| ≤ Real.log c := by
  have hc0 : 0 < c := by linarith
  rcases B.eq_empty_or_nonempty with rfl | hne
  · rw [Set.subset_empty_iff.1 hAB, sub_self, abs_zero]
    exact Real.log_nonneg hc
  obtain ⟨r0, hr0⟩ := hne
  have bB : BddBelow B := ⟨0, hB⟩
  have bA : BddBelow A := bB.mono hAB
  have h1 : sInf B ≤ sInf A := csInf_le_csInf bB ⟨_, hBA r0 hr0⟩ hAB
  have h2 : sInf A ≤ c * sInf B := by
    rw [← div_le_iff₀' hc0]
    exact le_csInf ⟨r0, hr0⟩ fun r hr => (div_le_iff₀' hc0).2 (csInf_le bA (hBA r hr))
  have h0 : 0 ≤ sInf B := le_csInf ⟨r0, hr0⟩ hB
  rcases h0.eq_or_lt with h | h
  · have : sInf A = sInf B := le_antisymm (by rw [← h] at h2 ⊢; simpa using h2) h1
    rw [this, sub_self, abs_zero]
    exact Real.log_nonneg hc
  · have h3 := Real.log_le_log h h1
    have h4 := Real.log_le_log (h.trans_le h1) h2
    rw [Real.log_mul hc0.ne' h.ne'] at h4
    rw [abs_of_nonneg (by linarith)]
    linarith

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

open MonObj in

theorem comb_smul {S : Type} [CommRing S] (a : S) {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) : IsCombAtG t x v (fun i => a * cf i) (spMap (epsMul a) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG x ⟶ tEpsG x := Over.homMk (spMap (epsMul a)) (by
    show spMap (epsMul a) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S (DualNumber S)) ≫ x
    rw [← Category.assoc, spMap_comp']
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, spMap_comp']
    congr 2
    refine RingHom.ext fun r => ?_
    ext
    · simp [epsMul]
    · simp [epsMul]
      ring
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

theorem abs_log_grNorm_sub_le (x : Sp C ⟶ X) {Λ Λ' : Set (Sp (DualNumber C) ⟶ t.G.left)} {a : C} (ha : a ≠ 0)
    (ha1 : ‖a‖ ≤ 1) (h1 : Λ ⊆ Λ') (h2 : ∀ v ∈ Λ', spMap (epsMul a) ≫ v ∈ Λ) {m : ℕ}
    (u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)) (i : Fin m) :
    |Real.log (grNorm t x Λ u i) - Real.log (grNorm t x Λ' u i)| ≤ Real.log ‖a‖⁻¹ := by
  refine abs_log_sInf_sub_le ((one_le_inv₀ (norm_pos_iff.2 ha)).2 ha1) ?_ ?_ ?_
  · rintro r ⟨cf, -, -, -, rfl⟩
    positivity
  · rintro r ⟨cf, h3, h4, ⟨w, hw, hc⟩, rfl⟩
    exact ⟨cf, h3, h4, ⟨w, h1 hw, hc⟩, rfl⟩
  · rintro r ⟨cf, h3, h4, ⟨w, hw, hc⟩, rfl⟩
    refine ⟨fun k => a * cf k, mul_ne_zero ha h3, fun k hk => by simp [h4 k hk], ⟨_, h2 w hw, comb_smul t a hc⟩, ?_⟩
    rw [norm_mul, mul_inv]

end Lat

section Ext

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem existsUnique_ext (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] (x : Sp C ⟶ Z.X) : ∃! xO : Sp ↥(intO C) ⟶ Z.X, spMap (intO C).subtype ≫ xO = x := by
  obtain ⟨-, xO, hx, -⟩ := GlobalTheory.ShFam.Pad.Test.latDR_nonempty Z x
  refine ⟨xO, hx, fun xO' hx' => ?_⟩
  have := isProper_toroidalModel_structureMap Z
  have hs : IsSeparated (terminal.from Z.X) := by
    rw [← terminal.comp_from Z.s]
    infer_instance
  let S : ValuativeCommSq (terminal.from Z.X) :=
    { R := intO C, K := C, i₁ := x, i₂ := terminal.from _, commSq := ⟨terminal.hom_ext _ _⟩ }
  have hu := IsSeparated.valuativeCriterion (terminal.from Z.X) S
  exact congrArg CommSq.LiftStruct.l
    (hu.elim ⟨xO', hx', terminal.hom_ext _ _⟩ ⟨xO, hx, terminal.hom_ext _ _⟩)

end Ext

end GlobalTheory.HTFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtDatLIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem atDat_lIntegral : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram →
    GlobalTheory.Mem.Top.Bl.AtDat fun _ B f T w Z hX Wt z => z.R.toRealDat.LIntegral := fun _ _ _ =>
  StepW.of_all fun _ _ _ _ _ _ _ _ _ _ _ z _ _ _ hG i =>
    ⟨z.geo.fw.ks i, GlobalTheory.GoodLat.mkFull_of_tie z.geo.fw hG.latFull i,
      GlobalTheory.RealGeoIn.mkStable_of_rhoGeo z.geo.fw z.geo.pins z.geo.rhoGeo i⟩

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLatticeCoordinates
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrCl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X}

def LCrd.frvecEmbL (D : LCrd M π) (α : D.C.A) {S : Type} [CommRing S] (z : Sp S ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) :
    TanM (z ≫ π) M.t.G →ₗ[S] (Fin (D.N + 1) → S) :=
  (Matrix.mulVecLin ((D.Em.A α).map (ev z _ h))).comp (D.crd α S z h)

theorem LCrd.frvec_emb_tanPull (D : LCrd M π) (α : D.C.A) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (z : Sp S ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) (h' : ⊤ ≤ (spMap φ ≫ z) ⁻¹ᵁ D.C.B α)
    (e : spMap φ ≫ z ≫ π = (spMap φ ≫ z) ≫ π) (v : TanM (z ≫ π) M.t.G) :
    D.emb α (spMap φ ≫ z) h' (tanPull φ e v) = φ ∘ D.emb α z h v := by
  unfold LCrd.emb
  rw [D.bc α S S' φ z _ rfl h h' e v, FlagMod.ev_spMap φ z _ h h']
  funext r
  rw [Function.comp_apply, RingHom.map_mulVec, Matrix.map_map]
  rfl

theorem LCrd.frvec_exists_emb_eq_smul (D : LCrd M π) (α β : D.C.A) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (hα : ⊤ ≤ z ⁻¹ᵁ D.C.B α) (hβ : ⊤ ≤ z ⁻¹ᵁ D.C.B β) :
    ∃ u : Sˣ, ∀ v, D.emb α z hα v = (u : S) • D.emb β z hβ v := by
  obtain ⟨u, hu⟩ := D.Em.compat α β S z hα hβ
  refine ⟨u, fun v => ?_⟩
  unfold LCrd.emb
  rw [← D.tr α β S z hα hβ v, Matrix.mulVec_mulVec]
  rw [hu]
  ext r
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem LCrd.frvec_emb_injective (D : LCrd M π) (α : D.C.A) {K : Type} [Field K] (z : Sp K ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α)
    (hz : Set.range z ⊆ π ⁻¹' Set.range M.j) : Function.Injective (D.frvecEmbL α z h) := by
  obtain ⟨A', hA'⟩ := D.Em.linv α
  have h1 : A'.map (ev z _ h) * (D.Em.A α).map (ev z _ h) = 1 := by
    rw [← Matrix.map_mul, hA', Matrix.map_one _ (map_zero _) (map_one _)]
  intro x y hxy
  simp only [LCrd.frvecEmbL, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply] at hxy
  have := congrArg (fun w => (A'.map (ev z _ h)).mulVec w) hxy
  simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this
  exact D.inj α K z h hz this

theorem frvec_initSpan_map {K P Q : Type} [Field K] [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q] {m : ℕ}
    (F : P →ₗ[K] Q) (v : Fin m → P) (e : ℕ) : initSpan K (fun i => F (v i)) e = (initSpan K v e).map F := by
  rw [initSpan, initSpan, Submodule.map_span, Set.image_image]

theorem frvec_initSpan_smul {K Q : Type} [Field K] [AddCommGroup Q] [Module K Q] {m : ℕ}
    (u : Kˣ) (v : Fin m → Q) (e : ℕ) : initSpan K (fun i => (u : K) • v i) e = initSpan K v e := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨j, hj, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rintro _ ⟨j, hj, rfl⟩
    have : v j = ((u⁻¹ : Kˣ) : K) • ((u : K) • v j) := by rw [smul_smul, Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

theorem frvec_initSpan_top {K Q : Type} [Field K] [AddCommGroup Q] [Module K Q] {m : ℕ}
    (v : Fin m → Q) : initSpan K v m = Submodule.span K (Set.range v) := by
  have : {j : Fin m | (j : ℕ) < m} = Set.univ := Set.eq_univ_of_forall fun j => j.2
  rw [initSpan, this, Set.image_univ]

theorem exists_isFrVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (D : LCrd M π) (σ : E →+* ℂ) (α : A.ch.ι → D.C.A), (∀ a, ⊤ ≤ A.ch.χ a ⁻¹ᵁ D.C.B (α a)) → ∃ (cv Dv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a), IsFrVec D A σ α cv ∧ (∀ a, LeftInv (Dv a) (cv a)) ∧ ∀ (K : Type) [Field K] (a a' : A.ch.ι) (φ : A.ch.R a →+* K) (φ' : A.ch.R a' →+* K), spMap φ ≫ A.ch.χ a = spMap φ' ≫ A.ch.χ a' → ∀ e : ℕ, e ∈ ty σ ∨ e = 0 ∨ e = Dw.mult σ → initSpan K (fun i => φ ∘ cv a i) e = initSpan K (fun i => φ' ∘ cv a' i) e := by
  intro E _ _ _ H Dw l Xo c V M X π ty A D σ α hα
  have hu : ∀ a, ∃ u : TVecs Dw M.t (A.ch.χ a ≫ π), up u = A.fr a :=
    fun a => exists_up fun σ i => ((A.frame a).1 σ i).1
  choose u₀ hu₀ using hu
  let cv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a :=
    fun a i => D.emb (α a) (A.ch.χ a) (hα a) (u₀ a σ i)
  have key : IsFrVec D A σ α cv := by
    intro a S _ φ z ez h u hup i
    subst ez
    have e' : spMap φ ≫ A.ch.χ a ≫ π = (spMap φ ≫ A.ch.χ a) ≫ π := (Category.assoc _ _ _).symm
    have hu : u = fun σ i => tanPull φ e' (u₀ a σ i) := by
      apply up_injective
      rw [up_tanPull, hu₀, hup]
    rw [hu]
    exact (D.frvec_emb_tanPull (α a) φ (A.ch.χ a) (hα a) h e' (u₀ a σ i)).symm
  have li : ∀ (a : A.ch.ι) (K : Type) [Field K] (φ : A.ch.R a →+* K),
      LinearIndependent K fun i => φ ∘ cv a i := by
    intro a K _ φ
    have h : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a) := FlagMod.le_preimage_comp _ (hα a)
    obtain ⟨u, hu⟩ := A.exists_up_fr (rfl : spMap φ ≫ A.ch.χ a = _)
    have hf := A.isFrame_bc (rfl : spMap φ ≫ A.ch.χ a = _)
    rw [← hu] at hf
    have hr : Set.range (spMap φ ≫ A.ch.χ a) ⊆ π ⁻¹' Set.range M.j := by
      rw [← A.cover]
      exact A.ch.range_subset rfl
    have := ((isFrame_up_iff _ _).1 hf σ).1.map' (D.frvecEmbL (α a) _ h)
      (LinearMap.ker_eq_bot.2 (D.frvec_emb_injective (α a) _ h hr))
    have e : (fun i => φ ∘ cv a i) = D.frvecEmbL (α a) _ h ∘ u σ := funext fun i => key a K φ _ rfl h u hu i
    rw [e]
    exact this
  have hD : ∀ a, ∃ Dv : Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a, LeftInv Dv (cv a) := by
    intro a
    obtain ⟨Q, hQ⟩ := GlobalTheory.matrix_exists_left_inverse_of_forall_field (A.ch.R a) (D.N + 1) (Dw.mult σ)
      (Matrix.of fun r i => cv a i r) fun K _ φ => by
        rw [Matrix.mulVec_injective_iff]
        exact li a K φ
    refine ⟨fun z r => Q z r, fun z z' => ?_⟩
    have := congrFun (congrFun hQ z) z'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Matrix.of_apply] at this
    convert this
  choose Dv hDv using hD
  refine ⟨cv, Dv, key, hDv, fun K _ a a' φ φ' hz e he => ?_⟩
  have h : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a) := FlagMod.le_preimage_comp _ (hα a)
  have h' : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a') := by
    rw [hz]; exact FlagMod.le_preimage_comp _ (hα a')
  obtain ⟨u, hu⟩ := A.exists_up_fr (rfl : spMap φ ≫ A.ch.χ a = _)
  obtain ⟨u', hu'⟩ := A.exists_up_fr hz.symm
  obtain ⟨s, hs⟩ := D.frvec_exists_emb_eq_smul (α a') (α a) _ h' h
  have e1 : (fun i => φ ∘ cv a i) = fun i => D.frvecEmbL (α a) _ h (u σ i) :=
    funext fun i => key a K φ _ rfl h u hu i
  have e2 : (fun i => φ' ∘ cv a' i) = fun i => (s : K) • D.frvecEmbL (α a) _ h (u' σ i) :=
    funext fun i => (key a' K φ' _ hz.symm h' u' hu' i).trans (hs _)
  rw [e1, e2, frvec_initSpan_smul, frvec_initSpan_map, frvec_initSpan_map]
  congr 1
  rcases he with he | rfl | rfl
  · have f1 := A.flagAt_fr (rfl : spMap φ ≫ A.ch.χ a = _)
    have f2 := A.flagAt_fr hz.symm
    rw [← hu] at f1
    rw [← hu'] at f2
    exact Atlas.FlagAt.initSpan_eq f1 f2 σ he
  · simp [initSpan]
  · have f1 := A.isFrame_bc (rfl : spMap φ ≫ A.ch.χ a = _)
    have f2 := A.isFrame_bc hz.symm
    rw [← hu] at f1
    rw [← hu', ← A.alg_eq rfl hz.symm] at f2
    rw [frvec_initSpan_top, frvec_initSpan_top, ((isFrame_up_iff _ _).1 f1 σ).2, ((isFrame_up_iff _ _).1 f2 σ).2]

end GlobalTheory.GrCl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasModelComparison
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

set_option autoImplicit false

namespace GlobalTheory.MapLoc

theorem exists_gen (X : Scheme.{0}) (x : X) (hd : IsDomain (X.presheaf.stalk x)) :
    ∃ ξ : X, ξ ⤳ x ∧ ∀ y, y ⤳ x → ξ ⤳ y := by
  let η : PrimeSpectrum (X.presheaf.stalk x) := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨X.fromSpecStalk x η, ?_, ?_⟩
  · have h1 : η ⤳ IsLocalRing.closedPoint (X.presheaf.stalk x) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal _) ≤ _ from bot_le)
    have := h1.map (X.fromSpecStalk x).continuous
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  · intro y hy
    have : y ∈ Set.range (X.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hy
    obtain ⟨q, rfl⟩ := this
    exact ((PrimeSpectrum.le_iff_specializes η q).1 (show (⊥ : Ideal _) ≤ _ from bot_le)).map
      (X.fromSpecStalk x).continuous

theorem isFractionRing_residue : ∀ (X : Scheme.{0}) (x ξ : X) (e : ξ ⤳ x), IsDomain (X.presheaf.stalk x) →
    (∀ y, y ⤳ ξ → y = ξ) →
    @IsFractionRing (X.presheaf.stalk x) _ (X.residueField ξ) _
      (RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom) :=
  GlobalTheory.T.isFractionRing_stalk_generic

theorem spMap_cancel {R K A : Type} [CommRing R] [CommRing K] [CommRing A] (f : R →+* K) (hf : Function.Injective f)
    (u v : Sp R ⟶ Sp A) (h : spMap f ≫ u = spMap f ≫ v) : u = v := by
  rw [← Spec.map_preimage u, ← Spec.map_preimage v] at h ⊢
  congr 1
  have e := Spec.map_injective ((Spec.map_comp _ _).trans (h.trans (Spec.map_comp _ _).symm))
  ext a
  exact hf (congrArg (fun φ => φ.hom a) e)

end GlobalTheory.MapLoc

open GlobalTheory.MapLoc in
theorem GlobalTheory.DRFlag.exists_mapsTo : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (Z : Mdl Y i₀), p.Prime → (p : ℂ) ∈ W.nonunits → Geo (Y i) π → i.c.F ≤ Z.i.c.F → (∀ σ, ty σ ⊆ Z.ty σ) → LocMaps Z A → ∃ h, MapsTo Z A h := by
  intro E _ _ _ H Dw Xo p W Y i₀ i X π ty A Z hp hW hgeo hF hty hloc

  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z.X := (geoOf Z).normal
  have : IsDiscreteValuationRing (Z.i.c.V W) := isDiscreteValuationRing_V _ W hp hW
  have hZp : IsProper Z.s := by
    have := projProper _ _ _ (geoOf Z).proj
    rwa [Z.π_s] at this
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  have : CompactSpace Z.X := QuasiCompact.compactSpace_of_compactSpace Z.s
  have : IsNoetherian Z.X := {}
  have hXp : IsProper (π ≫ (Y i).s) := projProper _ _ _ hgeo.proj
  have hopen : IsOpen Z.opn := by
    rw [← Z.cover]
    exact isOpen_iUnion fun a => (Z.U a).1.isOpen
  have hdom : ∀ x : Z.X, IsDomain (Z.X.presheaf.stalk x) := fun x => (hn x).1

  choose g hgx hgmin using fun x : Z.X => exists_gen Z.X x (hdom x)
  have hgo : ∀ x, g x ∈ Z.opn := fun x => by
    obtain ⟨g', hg', hg'x⟩ := GlobalTheory.ShFam.EigLoc.exists_generisation hopen Z.dense x
    exact (hgmin x g' hg'x).mem_open hopen hg'
  have hgen : ∀ x y, y ⤳ g x → y = g x := fun x y hy =>
    (hy.antisymm (hgmin x y (hy.trans (hgx x)))).eq

  let f : ∀ x : Z.X, Z.X.presheaf.stalk x →+* Z.X.residueField (g x) := fun x =>
    (Z.X.presheaf.stalkSpecializes (hgx x) ≫ Z.X.residue (g x)).hom
  have hfr : ∀ x, @IsFractionRing (Z.X.presheaf.stalk x) _ (Z.X.residueField (g x)) _ (f x).toAlgebra := fun x =>
    isFractionRing_residue Z.X x (g x) (hgx x) (hdom x) (hgen x)
  have hinj : ∀ x, Function.Injective (f x) := fun x => by
    letI := (f x).toAlgebra
    haveI := hfr x
    exact IsFractionRing.injective (Z.X.presheaf.stalk x) (Z.X.residueField (g x))
  have key : ∀ x, spMap (f x) ≫ Z.X.fromSpecStalk x = Z.X.fromSpecResidueField (g x) := fun x => by
    show Spec.map (_ ≫ _) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl

  have Hy : ∀ ξ : Z.opn, ∃ y : Sp (Z.X.residueField ξ.1) ⟶ X, NatTo Z A (Z.X.fromSpecResidueField ξ.1) y ∧
      ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] [Algebra R (Z.X.residueField ξ.1)]
        [IsFractionRing R (Z.X.residueField ξ.1)] (z : Sp R ⟶ Z.X),
        spMap (algebraMap R (Z.X.residueField ξ.1)) ≫ z = Z.X.fromSpecResidueField ξ.1 →
        ∃ z' : Sp R ⟶ X, spMap (algebraMap R (Z.X.residueField ξ.1)) ≫ z' = y := fun ξ =>
    hloc _ _ (by
      rintro _ ⟨q, rfl⟩
      exact Set.mem_of_eq_of_mem (Scheme.fromSpecResidueField_apply ξ.1 _) ξ.2)
  choose y hyN hyE using Hy

  have Hh : ∀ x : Z.X, ∃ z' : Sp (Z.X.presheaf.stalk x) ⟶ X, spMap (f x) ≫ z' = y ⟨g x, hgo x⟩ := fun x => by
    letI := (f x).toAlgebra
    haveI := hfr x
    haveI := hdom x
    haveI := (hn x).2
    exact hyE ⟨g x, hgo x⟩ (Z.X.presheaf.stalk x) (Z.X.fromSpecStalk x) (key x)
  choose h hh using Hh
  have hh' : ∀ x ξ (e : ξ ⤳ x), g x = ξ → ∀ hξ : ξ ∈ Z.opn,
      Spec.map (Z.X.presheaf.stalkSpecializes e ≫ Z.X.residue ξ) ≫ h x = y ⟨ξ, hξ⟩ := by
    rintro x ξ e rfl hξ
    exact hh x

  let b : i.c.V W →+* Z.i.c.V W :=
    ((IntermediateField.inclusion hF).toRingHom.comp (i.c.V W).subtype).codRestrict (Z.i.c.V W) fun x => x.2
  have hovr : ∀ {K : Type} [Field K] (w : Sp K ⟶ Z.X) (y' : Sp K ⟶ X), NatTo Z A w y' →
      y' ≫ π ≫ (Y i).s = w ≫ Z.s ≫ spMap b := by
    rintro K _ w y' ⟨τ, mu, u, ⟨b', π', r, hb', h1, h2, -⟩, he, -, -⟩
    have eb : b' = b := RingHom.ext fun v => Subtype.ext (Subtype.ext (hb' v))
    subst eb
    rw [← Category.assoc, he, ← h1, ← Z.π_s]
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% h2]
  have hover : ∀ x, h x ≫ π ≫ (Y i).s = Z.X.fromSpecStalk x ≫ Z.s ≫ spMap b := fun x => by
    apply spMap_cancel (f x) (hinj x)
    rw [← Category.assoc, hh x]
    exact (hovr (Z.X.fromSpecResidueField (g x)) (y ⟨g x, hgo x⟩) (hyN ⟨g x, hgo x⟩)).trans (by rw [← key x]; exact Category.assoc _ _ _)

  obtain ⟨gg, hgg⟩ := GlobalTheory.T.exists_morphism_of_stalk_maps (Sp (i.c.V W)) Z.X X (Z.s ≫ spMap b) (π ≫ (Y i).s) h inferInstance inferInstance
    inferInstance hn hover (by
      intro x ξ e hξ
      have hxg : g x = ξ := hξ _ (hgmin x ξ e)
      have hξg : g ξ = ξ := hξ _ (hgx ξ)
      have hξo : ξ ∈ Z.opn := hxg ▸ hgo x
      have hi : Function.Injective (Z.X.residue ξ).hom := by
        letI := (Z.X.presheaf.stalkSpecializes (specializes_refl ξ) ≫ Z.X.residue ξ).hom.toAlgebra
        haveI := isFractionRing_residue Z.X ξ ξ (specializes_refl ξ) (hdom ξ) hξ
        have := IsFractionRing.injective (Z.X.presheaf.stalk ξ) (Z.X.residueField ξ)
        rwa [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at this
      haveI : IsIso (Z.X.residue ξ) := (ConcreteCategory.isIso_iff_bijective _).2 ⟨hi, Scheme.residue_surjective _ _⟩
      rw [← cancel_epi (Spec.map (Z.X.residue ξ)), ← Category.assoc, ← Spec.map_comp, hh' x ξ e hxg hξo]
      have := hh' ξ ξ (specializes_refl ξ) hξg hξo
      rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at this
      exact this.symm)

  refine ⟨gg, fun k _ w hw => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x, w (IsLocalRing.closedPoint k) = x := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.ShFam.EigLoc.exists_stalk_factor w x (hx ▸ specializes_rfl)
  have hxo : x ∈ Z.opn := hx ▸ hw ⟨_, rfl⟩
  have e1 : w ≫ gg = spMap ψ ≫ h x := by rw [← hψ, Category.assoc, hgg]
  rw [e1, ← hψ]
  refine GlobalTheory.T.atlas_local_ring_points E H Dw Xo p W Y i₀ i X π ty A Z (Z.X.presheaf.stalk x) (Z.X.residueField (g x)) k (f x) ψ
    (Z.X.fromSpecStalk x) (h x) hF hty (hinj x) (by rw [Scheme.fromSpecStalk_closedPoint]; exact hxo) ?_
  rw [key x, hh x]
  exact hyN ⟨g x, hgo x⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainArithmeticGroupLocallyInjectiveStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDomain_arithmeticGroup_locally_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := by
  first | exact @GlobalTheory.LocInj.locInj | exact GlobalTheory.LocInj.locInj | (intros; apply GlobalTheory.LocInj.locInj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates : (∀ (S : Type) [CommRing S] (M k : ℕ) (ι ι' : Type) (D : ι' → Fin (M + 1) → S) (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι), ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det) ∧ ∀ (T : Type) (m : T → ℕ) (S : Type) [CommRing S] (M : ℕ) (D c : Let m → Fin (M + 1) → S) (w : Pm m) (x : CellVar m → S), LeftInv D c → (∀ (k : ℕ) (e : Fin k → Let m), Down e → ∑ q, lform D (wLet w ∘ e) q * plk (cellVec c w x) e q = 1) ∧ ∀ (τ : T) (i j : Fin (m τ)) (h : j < i), ∑ q, lform D (fun l : Fin (j + 1) => wLet w ⟨τ, if (l : ℕ) = j then i else Fin.castLE (Nat.succ_le_of_lt j.2) l⟩) q * plk (cellVec c w x) (std τ (j + 1) (Nat.succ_le_of_lt j.2)) q = x ⟨τ, ⟨(i, j), h⟩⟩ := by
  first | exact @GlobalTheory.FlagEmb.CauchyBinet.main | exact GlobalTheory.FlagEmb.CauchyBinet.main | (intros; apply GlobalTheory.FlagEmb.CauchyBinet.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartEmbeddingHoldsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_embedding_holds : GlobalTheory.LocM.Cht.EmbSt := by
  first | exact @GlobalTheory.LocM.Cht.embSt | exact GlobalTheory.LocM.Cht.embSt | (intros; apply GlobalTheory.LocM.Cht.embSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHoldsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_frame_base_holds : GlobalTheory.LocM.Cht.FrameBaseSt := by
  first | exact @GlobalTheory.LocM.FrameBase.frameBase | exact GlobalTheory.LocM.FrameBase.frameBase | (intros; apply GlobalTheory.LocM.FrameBase.frameBase <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupLeBaseLatticeLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_localGroup_le_baseLattice_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0 := by
  first | exact @GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base | exact GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base | (intros; apply GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRootsHoldsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_roots_holds : GlobalTheory.LocM.Cht.RootsSt := by
  first | exact @GlobalTheory.LocM.RootsPrescribe.roots | exact GlobalTheory.LocM.RootsPrescribe.roots | (intros; apply GlobalTheory.LocM.RootsPrescribe.roots <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramePointEigenframeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_point_eigenframe : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : A →+* ℂ), x ≫ genStr Z = spMap φ → ψ.comp φ = σ → (∀ s, (spMap ψ ≫ x) s ∉ genBd Z) → ∃ y : FrPt Xo c (CAt σ), Matches fr ψ y := by
  first | exact @GlobalTheory.ShFam.BdArc.exists_matches | exact GlobalTheory.ShFam.BdArc.exists_matches | (intros; apply GlobalTheory.ShFam.BdArc.exists_matches <;> assumption)
end

