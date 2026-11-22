import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2197
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSubextensionPoint
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

set_option autoImplicit false

namespace GlobalTheory.FinDesc

theorem spField_pt_eq (K : Type) [Field K] (a b : Sp K) : a = b := by
  have h : ∀ c : PrimeSpectrum K, c.asIdeal = ⊥ := fun c => Ideal.eq_bot_of_prime c.asIdeal
  exact PrimeSpectrum.ext ((h a).trans (h b).symm)

theorem exists_finite_subext_point : ∀ (X S : Scheme.{0}) (s : X ⟶ S), LocallyOfFiniteType s → ∀ (K₀ K : Type) [Field K₀]
    [Field K] [Algebra K₀ K], Algebra.IsAlgebraic K₀ K → ∀ (y : Sp K ⟶ X) (z : Sp K₀ ⟶ S),
    y ≫ s = spMap (algebraMap K₀ K) ≫ z → ∃ (L : IntermediateField K₀ K) (yL : Sp L ⟶ X), FiniteDimensional K₀ L ∧
      spMap (algebraMap L K) ≫ yL = y ∧ yL ≫ s = spMap (algebraMap K₀ L) ≫ z := by
  intro X S s hs K₀ K _ _ _ halg y z hyz
  classical
  let pb : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hpt : ∀ a : Sp K₀, z a = s (y pb) := fun a => by
    have e := congrArg (fun h : Sp K ⟶ S => h pb) hyz
    simp only [Scheme.Hom.comp_apply] at e
    rw [e, spField_pt_eq K₀ a]
  obtain ⟨U, hU, hqU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens)
    (show s (y pb) ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, hgV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show y pb ∈ s ⁻¹ᵁ U from hqU)
  have hU' : IsAffineOpen U := hU
  have hV' : IsAffineOpen V := hV
  have hry : Set.range y ⊆ Set.range hV'.fromSpec := by
    rw [hV'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    rw [spField_pt_eq K a pb]
    exact hgV
  have hrz : Set.range z ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    rw [hpt a]
    exact hqU
  have hy₁ := IsOpenImmersion.lift_fac hV'.fromSpec y hry
  have hz₁ := IsOpenImmersion.lift_fac hU'.fromSpec z hrz
  rw [← Spec.map_preimage (IsOpenImmersion.lift hV'.fromSpec y hry)] at hy₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec z hrz)] at hz₁
  set φ := Spec.preimage (IsOpenImmersion.lift hV'.fromSpec y hry) with hφ
  set ψ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec z hrz) with hψ
  have key : s.appLE U V hVU ≫ φ = ψ ≫ CommRingCat.ofHom (algebraMap K₀ K) := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec s hU' hV' hVU, ← Category.assoc, hy₁, hz₁]
    exact hyz
  have hft := LocallyOfFiniteType.finiteType_appLE s hU' hV' hVU
  let _ := (s.appLE U V hVU).hom.toAlgebra
  obtain ⟨T, hT⟩ := hft.out
  let L : IntermediateField K₀ K := IntermediateField.adjoin K₀ ((T.image φ.hom : Finset K) : Set K)
  have hfin : FiniteDimensional K₀ L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (halg.isAlgebraic x).isIntegral
  have hmem : ∀ b : Γ(X, V), φ.hom b ∈ L := by
    intro b
    have hb : b ∈ Algebra.adjoin Γ(S, U) (T : Set Γ(X, V)) := by rw [hT]; exact Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem b hb => exact IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb))
    | algebraMap a =>
      have e := congrArg (fun h => h.hom a) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
      rw [RingHom.algebraMap_toAlgebra, e]
      exact L.algebraMap_mem _
    | add b c _ _ hb hc => rw [map_add]; exact L.add_mem hb hc
    | mul b c _ _ hb hc => rw [map_mul]; exact L.mul_mem hb hc
  let φL : Γ(X, V) →+* L := φ.hom.codRestrict L hmem
  refine ⟨L, Spec.map (CommRingCat.ofHom φL : Γ(X, V) ⟶ CommRingCat.of L) ≫ hV'.fromSpec, hfin, ?_, ?_⟩
  · rw [← hy₁, ← Category.assoc]
    congr 1
    rw [spMap, ← Spec.map_comp]
    congr 1
  · have key' : s.appLE U V hVU ≫ CommRingCat.ofHom φL = ψ ≫ CommRingCat.ofHom (algebraMap K₀ L) := by
      ext a
      have e := congrArg (fun h => h.hom a) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e ⊢
      exact e
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec s hU' hV' hVU, ← Category.assoc, ← Spec.map_comp, key',
      Spec.map_comp, ← hz₁, spMap]
    simp only [Category.assoc]

end GlobalTheory.FinDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapEqOfGroupInvariant
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep

theorem functionFieldMap_germToFunctionField {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
    (f : X ⟶ X') [IsDominant f] (V : X'.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) [Nonempty U]
    [Nonempty V] (s : Γ(X', V)) :
    functionFieldMap f (X'.germToFunctionField V s) = X.germToFunctionField U (f.appLE V U e s) := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hfx : f (genericPoint X) ∈ V := e hx
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X') hfx, functionFieldMap_algebraMap,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hx]
  congr 1
  exact (Scheme.Hom.germ_stalkMap_apply f V _ hfx s).trans
    (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE e) _ hx (f.app V s)).symm

theorem exists_functionFieldMap_eq_of_invariant (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W]
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q]
    (h : IsAffineQuotient ρ q) (u : X.functionFieldˣ) (hu : ∀ γ, fnAct ρ γ u = u) :
    ∃ b : W.functionFieldˣ, Units.map (functionFieldMap q).toMonoidHom b = u := by
  classical
  have := Fintype.ofFinite Γ
  have := h.isAffineHom
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  haveI : Nonempty V := ⟨⟨_, hyV⟩⟩
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := (show IsAffineOpen V from hV).preimage q
  obtain ⟨x, hx⟩ := q.denseRange.exists_mem_open V.isOpen ⟨_, hyV⟩
  haveI : Nonempty (q ⁻¹ᵁ V) := ⟨⟨x, hx⟩⟩
  have hst := h.preimage_le V
  haveI (γ : Γ) : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  haveI := functionField_isFractionRing_of_isAffineOpen X _ hU
  let σ : Γ → Γ(X, q ⁻¹ᵁ V) →+* Γ(X, q ⁻¹ᵁ V) := fun γ ↦ ((ρ γ).hom.appLE _ _ (hst γ)).hom
  have hσ (γ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) :
      functionFieldMap (ρ γ).hom (algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField s) =
        algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField (σ γ s) :=
    functionFieldMap_germToFunctionField _ _ _ (hst γ) s
  have hσ1 (s : Γ(X, q ⁻¹ᵁ V)) : σ 1 s = s := by
    have e1 : (ρ 1).hom = 𝟙 X := by rw [map_one]; rfl
    change (ρ 1).hom.appLE _ _ (hst 1) s = s
    simp only [e1]
    exact congr($(X.presheaf.map_id (Opposite.op (q ⁻¹ᵁ V))) s)
  have hσmul (γ δ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) : σ δ (σ γ s) = σ (γ * δ) s := by
    have e2 : (ρ (γ * δ)).hom = (ρ δ).hom ≫ (ρ γ).hom := by rw [map_mul]; rfl
    change (ρ δ).hom.appLE _ _ (hst δ) ((ρ γ).hom.appLE _ _ (hst γ) s) =
      (ρ (γ * δ)).hom.appLE _ _ (hst (γ * δ)) s
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, e2]
  set e := algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField with he_def
  have einj : Function.Injective e := IsFractionRing.injective _ _
  have hfu (δ : Γ) : functionFieldMap (ρ δ).hom (u : X.functionField) = u :=
    congrArg Units.val (hu δ)
  obtain ⟨a, t, ht, hat⟩ := IsFractionRing.div_surjective (A := Γ(X, q ⁻¹ᵁ V)) (u : X.functionField)
  have ht0 : e t ≠ 0 := by
    rw [Ne, ← map_zero e]
    exact fun h0 ↦ nonZeroDivisors.ne_zero ht (einj h0)
  let N := ∏ γ, σ γ t
  have hN (δ : Γ) : σ δ N = N := by
    simp only [N, map_prod, hσmul]
    exact Fintype.prod_equiv (Equiv.mulRight δ) _ _ (fun _ ↦ rfl)
  have hNe : e N ≠ 0 := by
    simp only [N, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun γ _ ↦ ?_
    rw [← hσ]
    exact (map_ne_zero _).mpr ht0
  let c := a * ∏ γ ∈ Finset.univ.erase 1, σ γ t
  have hc : e c = u * e N := by
    have hsplit : N = t * ∏ γ ∈ Finset.univ.erase 1, σ γ t := by
      simp only [N]
      rw [← Finset.mul_prod_erase Finset.univ (fun γ ↦ σ γ t) (Finset.mem_univ 1), hσ1]
    rw [← he_def] at hat
    rw [hsplit]
    simp only [c, map_mul]
    rw [← hat]
    field_simp
  have hcinv (δ : Γ) : σ δ c = c := by
    apply einj
    rw [← hσ, hc, map_mul, hfu, hσ, hN]
  obtain ⟨bc, hbc⟩ := h.mem_range_app V c fun δ ↦ ⟨hst δ, hcinv δ⟩
  obtain ⟨bN, hbN⟩ := h.mem_range_app V N fun δ ↦ ⟨hst δ, hN δ⟩
  have hq (b : Γ(W, V)) : functionFieldMap q (W.germToFunctionField V b) = e (q.app V b) := by
    rw [Scheme.Hom.app_eq_appLE]
    exact functionFieldMap_germToFunctionField q V (q ⁻¹ᵁ V) le_rfl b
  have hbN0 : W.germToFunctionField V bN ≠ 0 := by
    intro h0
    apply hNe
    rw [← hbN, ← hq, h0, map_zero]
  have hbc0 : W.germToFunctionField V bc ≠ 0 := by
    intro h0
    apply mul_ne_zero u.ne_zero hNe
    rw [← hc, ← hbc, ← hq, h0, map_zero]
  refine ⟨Units.mk0 (W.germToFunctionField V bc / W.germToFunctionField V bN)
    (div_ne_zero hbc0 hbN0), Units.ext ?_⟩
  simp only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    map_div₀, hq, hbc, hbN, hc]
  field_simp

end GlobalTheory.OrbitSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChart
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels Formalism.L2.Pj
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)

namespace GlobalTheory.KeyFramePoint

open scoped CategoryTheory.MonObj in

theorem card_eq_of_isLieBasis {X : Scheme.{0}} {R : Type} [CommRing R] [Nontrivial R] {x : Sp R ⟶ X} {G : Over X} [GrpObj G]
    [IsCommMonObj G] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G x Φ) {n n' : ℕ} {v : Fin n → (epsR R ⟶ G')} {v' : Fin n' → (epsR R ⟶ G')}
    (hb : IsLieBasis v) (hb' : IsLieBasis v') : n = n' := by
  obtain ⟨b₁⟩ := GlobalTheory.KeyAtEx.nonempty_basis_of_isLieBasis h hb
  obtain ⟨b₂⟩ := GlobalTheory.KeyAtEx.nonempty_basis_of_isLieBasis h hb'
  simpa using Fintype.card_congr (b₁.indexEquiv b₂)

theorem exists_keyAt_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : GChart Y) (V K : Type) [CommRing V] [IsLocalRing V] [Field K] [CharZero K] [Algebra V K] (yt : Sp V ⟶ Y.X) (hz : ⊤ ≤ yt ⁻¹ᵁ M.U) (t : SAB H (Sp V)) (_ : SABMap t Y.t yt) (n : ℕ) (w : Fin n → (epsR V ⟶ t.G)), IsLieBasis w → ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) → Generates (X := t.G) θ → ∃ (x' : KeyIn K) (a d : Vˣ), KeyAt M (spMap (algebraMap V K) ≫ yt) (le_preimage_comp _ hz) x' ∧ ∀ κ : KeyRule, IsKeyRule κ → algebraMap V K a ^ 8 * (κ K x' : K) = algebraMap V K d ^ 4 * (κ K x : K) := by
  intro E _ _ _ H D l Xo c O _ β Y M V K _ _ _ _ _ yt hz t m n w hw θ x hx hgen
  obtain ⟨w₁, θM, ⟨hw₁, hr₁⟩, hth, hne⟩ :=
    GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t yt m M.U hz M.θ M.θ_mem M.θ_ne
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t Y.t (spMap (ev yt M.U hz) ≫ M.hU.fromSpec), m'.φ = m.φ := by
    rw [GlobalTheory.FlagMod.spMap_ev yt M.hU hz]
    exact ⟨m, rfl⟩
  obtain ⟨vM, hvM, hbM, -⟩ := M.lie V (ev yt M.U hz) t m'
  rw [hm'] at hvM
  have he : eSec t.G ≫ m.φ = yt ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ eSec Y.t.G) m.base)
  have hrig : m.cm.rigPull Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ yt he Y.t.PP.L Y.t.PP.rig := by
    have key : ∀ (a b : Sp V ⟶ Y.X) (_ : a = b) ha hb,
        rigPullOf (G' := t.G) m.φ a ha Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ b hb Y.t.PP.L Y.t.PP.rig := by
      rintro a b rfl _ _
      rfl
    exact key _ _ m.base _ _
  rw [hrig] at hr₁

  obtain ⟨a, ha, -⟩ := hgen θM
  have hau : IsUnit a := by
    obtain ⟨g, i, h₁, h₂⟩ := hne (IsLocalRing.closedPoint V)
    exact (NonzeroClosed.of_isMul ha ⟨g, h₁, Opens.mem_iSup.2 ⟨i, h₂⟩⟩).1
  obtain ⟨a, rfl⟩ := hau

  obtain ⟨P, hP, rig, hrig', th, hthne, v, hv⟩ := x
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := hx
  dsimp only at φ' he' w' hg' hp' hw' hr' hs' hv'
  subst hg'
  have hn : P.g = M.n := card_eq_of_isLieBasis m.cart hw hbM
  have hbM' : IsLieBasis (fun i : Fin P.g => vM (i.cast hn)) := by
    have key : ∀ (k : ℕ) (h : k = M.n), IsLieBasis (fun i : Fin k => vM (i.cast h)) := by
      rintro k rfl
      exact hbM
    exact key _ hn
  choose Mat hMat using fun i : Fin P.g => (hw.2 _ (hbM'.1 i)).exists
  obtain ⟨d, hd⟩ : IsUnit (Matrix.det (Matrix.of Mat)) :=
    ((GlobalTheory.LieComb.lieComb_algebra V t.G P.g w hw.1).2.2.2.2 (Matrix.of Mat) _ hw hMat).1 hbM'
  haveI := P.isAb.comm
  obtain ⟨ex, -, -, -, bas⟩ := GlobalTheory.LieComb.lieComb_algebra K P.A P.g v hv.1
  choose v' hvv' using fun i => (ex (((Matrix.of Mat).map (algebraMap V K)) i)).exists
  have hdet : ((Matrix.of Mat).map (algebraMap V K)).det = algebraMap V K d := by
    rw [hd, RingHom.map_det]; rfl
  have hb' : IsLieBasis v' := (bas _ v' hv hvv').2 (hdet ▸ d.isUnit.map _)
  obtain ⟨th', e₀, -, hle⟩ := GlobalTheory.KeyPow.exists_sec_div P.A.hom (a := algebraMap V K (a⁻¹ : Vˣ)) (b := algebraMap V K a)
    (by rw [← map_mul, Units.inv_mul, map_one]) th
  have hth' : ∀ s : Sp K, ∃ y : P.A.left, P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th' :=
    fun s => (hthne s).imp fun y hy => ⟨hy.1, hle hy.2⟩
  refine ⟨⟨P, hP, rig, hrig', th', hth', v', hb'⟩, a, d, ?_, fun κ hκ => ?_⟩
  swap
  · rw [← hdet]
    exact hκ.1 K P hP rig hrig' th hthne v hv th' hth' v' hb' _ _ e₀ hvv'
  have g := (isGen_iff w₁).1 hw₁
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp t.PP.isLB w₁ w' g g' Y.t.PP.isLB P.isLB
  have he'' : eSec P.A ≫ φ' ≫ m.φ = (spMap (algebraMap V K) ≫ yt) ≫ eSec Y.t.G := by
    rw [← Category.assoc, he', Category.assoc, he, Category.assoc]
  have hF : F' = dualMap (algebraMap V K) := KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [hF']
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [hε']
      ext <;> simp [dualMap])
  have hq := hp'.comp m.cart
  refine ⟨φ' ≫ m.φ, he'', w'', hn, hq, (isGen_iff w'').2 (T.pgen_comp t.PP.isLB g g'), ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w₁ _ (fun _ => eSec Y.t.G) _ t.PP.rig Y.t.PP.rig yt _
      (rigPull_le m.φ yt he Y.t.PP.L) (fun _ => rfl)).1 hr₁
    have r₁ := (maps_iff w' _ (fun _ => eSec t.G) _ rig t.PP.rig (spMap (algebraMap V K)) _
      (rigPull_le φ' (spMap (algebraMap V K)) he' t.PP.L) (fun _ => rfl)).1 hr'
    exact (maps_iff w'' _ (fun _ => eSec Y.t.G) _ rig Y.t.PP.rig (spMap (algebraMap V K) ≫ yt) _
      (rigPull_le (φ' ≫ m.φ) (spMap (algebraMap V K) ≫ yt) he'' Y.t.PP.L) (fun _ => rfl)).2
      (T.pmaps_comp t.PP.isLB (fun _ => he') r₀ r₁)
  · refine (KeyAtBC.appLE_eq_iff_stalk w'' (KeyAtBC.mem_of_comm hq.1.w (le_preimage_comp _ hz)) M.θ th').2
      fun Z q y j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart t.PP.isLB (φ' (q y))
    have a₁ := (KeyAtBC.appLE_eq_iff_stalk w₁ (KeyAtBC.mem_of_comm m.cart.1.w hz) M.θ θM).1 (fun j i h =>
      (hth (j PUnit.unit) i _ h le_rfl).trans (congrArg (· * _) (GlobalTheory.LB.resG_self _ _))) Z (q ≫ φ') y j i hj hi
    have b₁ := (KeyCancel.appLE_eq_iff_stalk w' θ th).1 hs' Z q y i k hi hk
    have c₁ : gs (q ≫ φ') y _ (θM.f i) = cst ((q ≫ φ') ≫ t.G.hom) y a * gs (q ≫ φ') y _ (θ.f i) := by
      rw [ha i, gs_mul _ y _ hi, gs_constFn _ _ _ y hi]
    have c₂ : gs q y _ (th'.f k) = cst (q ≫ P.A.hom) y (algebraMap V K a) * gs q y _ (th.f k) := by
      rw [e₀ k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk]
    rw [Category.assoc, hp'.1.w, ← Category.assoc, cst_comp] at c₁
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a₁, c₁, b₁, c₂, Units.val_mul]
    ring
  · have e := (GlobalTheory.lieComb_baseChange V K (algebraMap V K) t.G P.A φ' hp' P.g w (vM (i.cast hn)) (Mat i) v (v' i)
      (fun j => (hv' j).trans (by rw [hF]; rfl)) (hMat i)).2 (hvv' i)
    rw [← Category.assoc, e, Category.assoc, hvM, FlagMod.ev_spMap _ yt M.U hz, FlagMod.dualMap_comp,
      KeyAtBC.spMap_comp₀, Category.assoc]
    rfl

end GlobalTheory.KeyFramePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFormParameterOfDiscreteNorms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem exists_form_of_discrete_norms : ∀ (C : Type) [NormedField C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ) (t : C), N.Int q → t ≠ 0 → ‖t‖ < 1 → (∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖t‖ ^ n) → ∀ m : ℕ, 1 ≤ m → ∃ (β : N.Form (m ^ 2)) (π : C), π ≠ 0 ∧ ‖π‖ < 1 ∧ (∀ n : ℕ, {α | (β.be α α / (2 * m ^ 2)).toNat = n}.Finite) ∧ ∀ α, Real.exp (-(q α / (m : ℝ) ^ 2)) = ‖π‖ ^ (β.be α α / (2 * m ^ 2)).toNat := by
  intro C _ _ N q t hI ht0 ht1 hψ m hm
  have htpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  set L : ℝ := -Real.log ‖t‖ with hL
  have hLpos : 0 < L := by
    have := Real.log_neg htpos ht1
    linarith
  clear_value L
  choose Q hQ using hψ
  have hq : ∀ χ, q χ = (Q χ : ℝ) * L := by
    intro χ
    have h1 := hI.ψ χ
    rw [hQ χ] at h1
    have h2 : Real.log (‖t‖ ^ Q χ) = -q χ := by rw [h1, Real.log_exp]
    rw [Real.log_zpow] at h2
    rw [hL]; linarith
  set Bf : N.X → N.X → ℤ := fun x y => Q (x + y) - Q x - Q y with hBf
  have hB : ∀ x y, (Bf x y : ℝ) = QuadraticMap.polar q x y / L := by
    intro x y
    rw [eq_div_iff hLpos.ne']
    simp only [hBf, QuadraticMap.polar, hq]
    push_cast; ring
  have inj : ∀ a b : ℤ, (a : ℝ) = b → a = b := fun a b h => Int.cast_inj.1 h
  let Bm : LinearMap.BilinForm ℤ N.X := LinearMap.mk₂ ℤ Bf
    (fun x x' y => inj _ _ (by rw [Int.cast_add, hB, hB, hB, QuadraticMap.polar_add_left, add_div]))
    (fun c x y => inj _ _ (by rw [smul_eq_mul, Int.cast_mul, hB, hB, QuadraticMap.polar_smul_left, zsmul_eq_mul, mul_div_assoc]))
    (fun x y y' => inj _ _ (by rw [Int.cast_add, hB, hB, hB, QuadraticMap.polar_add_right, add_div]))
    (fun c x y => inj _ _ (by rw [smul_eq_mul, Int.cast_mul, hB, hB, QuadraticMap.polar_smul_right, zsmul_eq_mul, mul_div_assoc]))
  have hBm : ∀ x y, Bm x y = Bf x y := fun x y => rfl
  have hdiag : ∀ x, Bf x x = 2 * Q x := by
    intro x
    apply inj
    rw [hB, QuadraticMap.polar_self, hq, nsmul_eq_mul]
    push_cast
    field_simp
    try ring
  have hsymm : ∀ x y, Bf x y = Bf y x := by
    intro x y; simp only [hBf, add_comm x y]; ring
  have hpos : ∀ y, y ≠ 0 → 0 < q y := by
    intro y hy
    by_contra hn
    push_neg at hn
    have hfin : {α | ¬ (0 < q α)}.Finite :=
      Filter.eventually_cofinite.1 (hI.pos.eventually (Filter.eventually_gt_atTop 0))
    have hinf : (Set.range fun c : ℤ => c • y).Infinite :=
      Set.infinite_range_of_injective (smul_left_injective ℤ hy)
    refine hinf (hfin.subset ?_)
    rintro _ ⟨c, rfl⟩
    simp only [Set.mem_setOf_eq, not_lt]
    rw [QuadraticMap.map_smul, zsmul_eq_mul]
    push_cast
    nlinarith [mul_self_nonneg (c : ℝ)]
  have hQnn : ∀ y, 0 ≤ Q y := by
    intro y
    by_cases hy : y = 0
    · subst hy
      have : (Q 0 : ℝ) * L = 0 := by rw [← hq, QuadraticMap.map_zero]
      have : (Q 0 : ℝ) = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd h hLpos.ne'
      exact_mod_cast this.ge
    · have := hpos y hy
      rw [hq] at this
      have : (0 : ℝ) < Q y := pos_of_mul_pos_left this hLpos.le
      exact_mod_cast this.le
  have hQpos : ∀ y, y ≠ 0 → 0 < Q y := by
    intro y hy
    have := hpos y hy
    rw [hq] at this
    have : (0 : ℝ) < Q y := pos_of_mul_pos_left this hLpos.le
    exact_mod_cast this
  have hm0 : (2 * (m : ℤ) ^ 2) ≠ 0 := by positivity
  let β : N.Form (m ^ 2) :=
    { be := (2 * (m : ℤ) ^ 2) • Bm
      symm := fun y z => by
        simp only [LinearMap.smul_apply, hBm, hsymm y z]
      pos := fun y hy => by
        simp only [LinearMap.smul_apply, hBm, hdiag, smul_eq_mul]
        have := hQpos y hy
        positivity
      dvd := fun y z => ⟨Bf y z, by simp [LinearMap.smul_apply, hBm, smul_eq_mul]⟩ }
  have hβ : ∀ α, β.be α α / (2 * m ^ 2) = 2 * Q α := by
    intro α
    show ((2 * (m : ℤ) ^ 2) • Bm) α α / (2 * m ^ 2) = 2 * Q α
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hBm, hdiag, Int.mul_ediv_cancel_left _ hm0]
  have hn : 0 < 2 * m ^ 2 := by positivity
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq t hn
  have hπ0 : π ≠ 0 := by rintro rfl; exact ht0 (by rw [← hπ, zero_pow hn.ne'])
  have hπn : ‖π‖ ^ (2 * m ^ 2) = ‖t‖ := by rw [← norm_pow, hπ]
  have hπpos : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  have hπ1 : ‖π‖ < 1 := by
    by_contra h
    push_neg at h
    have := one_le_pow₀ (n := 2 * m ^ 2) h
    rw [hπn] at this
    linarith
  have hlp : Real.log ‖π‖ * (2 * (m : ℝ) ^ 2) = -L := by
    rw [hL, ← hπn, Real.log_pow]; push_cast; ring
  refine ⟨β, π, hπ0, hπ1, fun n => ?_, fun α => ?_⟩
  · have hfin : {α | ¬ ((n : ℝ) * L < q α)}.Finite :=
      Filter.eventually_cofinite.1 (hI.pos.eventually (Filter.eventually_gt_atTop _))
    refine hfin.subset fun α hα => ?_
    simp only [Set.mem_setOf_eq, hβ] at hα ⊢
    rw [not_lt, hq]
    have h1 : (2 * Q α) = (n : ℤ) := by
      rw [← hα, Int.toNat_of_nonneg (by linarith [hQnn α])]
    have h2 : (Q α : ℝ) ≤ n := by
      have : Q α ≤ (n : ℤ) := by linarith [hQnn α]
      exact_mod_cast this
    nlinarith
  · have hc : ((2 * Q α).toNat : ℝ) = 2 * (Q α : ℝ) := by
      have := Int.toNat_of_nonneg (show 0 ≤ 2 * Q α by linarith [hQnn α])
      exact_mod_cast this
    rw [hβ, ← Real.exp_log hπpos, ← Real.exp_nat_mul, hc, hq]
    congr 1
    have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm
      positivity
    have e : Real.log ‖π‖ = -L / (2 * (m : ℝ) ^ 2) := by
      rw [eq_div_iff (by positivity)]; exact hlp
    rw [e]
    field_simp

end GlobalTheory.MBLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedPointCompletionIndexOneStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralFramedPoint_completion_index_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ (Z : Comp Xo c) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (w : HeightOneSpectrum (𝓞 c.F)) (𝔭 : HeightOneSpectrum (𝓞 K)), (∀ a : c.F, vLa 𝔭 (algebraMap c.F K a) = vLa w a) → ∃ (T : CDVR) (ι : c.F →+* T.Fr) (y' : IntFr Xo c T ι), OverLa w T.V ι 1 ∧ algOn Z T ι y' := by
  first | exact @GlobalTheory.CompletionPoint.exists_intFr_index_one | exact GlobalTheory.CompletionPoint.exists_intFr_index_one | (intros; apply GlobalTheory.CompletionPoint.exists_intFr_index_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnColumnsSameValueStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_germ_on_columns_same_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ (N k : ℕ) (g : PS X.C n (chD Ch.ch)), MvIsInt (vX_vp X) g → ∃ f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C, MvIsInt (vX_vp X) f ∧ (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g - derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f)) := by
  first | exact @GlobalTheory.ColApprox.exists_germ_cols | exact GlobalTheory.ColApprox.exists_germ_cols | (intros; apply GlobalTheory.ColApprox.exists_germ_cols <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnCopiesSameValueStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_germ_on_copies_same_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ (N k : ℕ) (f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C), MvIsInt (vX_vp X) f → ∃ g : PS X.C n (chD Ch.ch), MvIsInt (vX_vp X) g ∧ (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g - derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f)) := by
  first | exact @GlobalTheory.ColumnGerm.exists_germ_on_copies | exact GlobalTheory.ColumnGerm.exists_germ_on_copies | (intros; apply GlobalTheory.ColumnGerm.exists_germ_on_copies <;> assumption)
end

