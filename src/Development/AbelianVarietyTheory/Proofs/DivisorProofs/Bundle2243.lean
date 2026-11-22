import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NumPull

theorem interNumRed_pull_curve {k : Type} [Field k] {M W : Scheme.{0}} (p : W ⟶ Sp k)
    (f : M ⟶ W) [IsProper p] (C : Closeds M) :
    letI := algebraΓOfHom p
    letI := algebraΓOfHom (f ≫ p)
    IsCompleteCurve k C →
    (∀ L : LB W, L.IsLB → interNumRed k C ![L.pull f] = 0) ∨
    ∃ C' : Closeds W, IsCompleteCurve k C' ∧ ∃ d : ℕ, ∀ L : LB W, L.IsLB →
      interNumRed k C ![L.pull f] = d * interNumRed k C' ![L] := by
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (f ≫ p)
  intro hC
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red hC.isIrreducible
  letI : Algebra k Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) :=
    algebraΓOfHom (redι C ≫ f ≫ p)
  let g := redι C ≫ f
  have hsM : strHom k M = f ≫ p := strHom_eq (fun _ => rfl)
  have hsW : strHom k W = p := strHom_eq (fun _ => rfl)
  have hsZ : strHom k (Scheme.IdealSheafData.vanishingIdeal C).subscheme = g ≫ p :=
    (strHom_eq (f := redι C ≫ f ≫ p) (fun _ => rfl)).trans (Category.assoc _ _ _).symm
  have hpZ : IsProper (strHom k (Scheme.IdealSheafData.vanishingIdeal C).subscheme) := by
    have := hC.isProper
    rw [hsM] at this
    rw [hsZ, Category.assoc]
    exact this
  have : IsProper (g ≫ p) := hsZ ▸ hpZ
  have : IsProper g := .of_comp g p
  have hd : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal C).subscheme = 1 :=
    (topologicalKrullDim_red C).trans hC.dim_eq
  have : CompactSpace (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (strHom k _)
  have := isNoetherian_of_locallyOfFiniteType_field
    (strHom k (Scheme.IdealSheafData.vanishingIdeal C).subscheme)
  have hdeg : ∀ L : LB W, L.IsLB → interNumRed k C ![L.pull f] = topSelfIntersection k (L.pull g) 1 := by
    intro L hL
    have hL' := pull_isLB hL f
    refine (interNumOn_eq_interNum_pull (appTop_algebraΓOfHom (redι C) (f ≫ p) rfl)
      (isLB_vecOne hL')).trans ?_
    refine interNum_congr_cls k _ (fun i => by fin_cases i; exact pull_isLB hL' _)
      (fun _ => pull_isLB hL g) fun i => ?_
    fin_cases i
    refine (cls_pull hL' _ _).trans ?_
    refine Eq.trans ?_ (cls_pull hL g _).symm
    rw [cls_pull hL f]
    exact (pull_comp (redι C) f _).symm
  by_cases hc : ∀ z, g z = g (genericPoint _)
  · left
    intro L hL
    rw [hdeg L hL]
    exact ArInt.topSelf_pull_eq_zero_of_const k hL g _ hc
  push_neg at hc
  obtain ⟨x₀, hx₀⟩ := hc
  right
  let φ := g.toImage
  have e : φ ≫ g.imageι = g := g.toImage_imageι
  have : IsProper (φ ≫ g.imageι) := by rw [e]; infer_instance
  have : IsProper φ := .of_comp φ g.imageι
  have hne : φ x₀ ≠ φ (genericPoint _) := fun h => hx₀ (by
    rw [← e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h])
  have : LocallyQuasiFinite φ := ProperCurve.locallyQuasiFinite_of_ne hd φ hne
  have : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  have hdense : DenseRange φ := g.toImage.denseRange
  have hsurj : Function.Surjective φ := by
    rw [← Set.range_eq_univ, ← φ.isClosedMap.isClosed_range.closure_eq]
    exact hdense.closure_range
  have hgen : φ (genericPoint _) = genericPoint g.image := by
    have h₁ := (genericPoint_spec (Scheme.IdealSheafData.vanishingIdeal C).subscheme).image
      φ.continuous
    rw [Set.image_univ, hdense.closure_range] at h₁
    exact h₁.eq (genericPoint_spec _)
  have hdZ : topologicalKrullDim g.image = 1 :=
    le_antisymm ((PosBaseChange.dim_le_of_isClosedMap φ.isClosedMap hsurj).trans hd.le)
      (ArInt.one_le_dim (genericPoint_specializes (φ x₀)) fun h => hne (h.symm.trans hgen.symm))
  letI : Algebra k Γ(g.image, ⊤) := algebraΓOfHom (g.imageι ≫ p)
  have hf : ∀ r : k, φ.appTop (algebraMap k Γ(g.image, ⊤) r) =
      algebraMap k Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) r :=
    appTop_algebraΓOfHom φ (g.imageι ≫ p) (by rw [reassoc_of% e]; exact Category.assoc _ _ _)
  have hsI : strHom k g.image = g.imageι ≫ p := strHom_eq (fun _ => rfl)
  have : IsProper (strHom k g.image) := by rw [hsI]; infer_instance
  have hproj : IsProjOver (strHom k g.image) := ProperCurve.isProjOver_of_isProper _ hdZ
  have : IsProper (g.imageι ≫ strHom k W) := by rw [hsW]; infer_instance
  refine ⟨⟨Set.range g.imageι, g.imageι.isClosedEmbedding.isClosed_range⟩,
    isCompleteCurve_range g.imageι hdZ, φ.residueDegree (genericPoint _), fun L hL => ?_⟩
  have hN := pull_isLB hL g.imageι
  have h₁ := ProjFin.interNumOn_eq_residueDegree_mul k g.image _ φ hproj hdZ hgen
    (L.pull g.imageι) hN
  have h₂ := interNumOn_eq_interNum_pull (k := k) (L := ![L.pull g.imageι]) hf (isLB_vecOne hN)
  have h₃ : topSelfIntersection k (L.pull g) 1 = interNum k (structureModule _)
      fun i => (![L.pull g.imageι] i).pull φ := by
    refine interNum_congr_cls _ _ (fun _ => pull_isLB hL g)
      (fun i => by fin_cases i; exact pull_isLB hN φ) fun i => ?_
    fin_cases i
    refine (cls_pull hL g _).trans ?_
    refine Eq.trans ?_ (cls_pull hN φ _).symm
    exact (congrArg (fun f => pull f (cls L hL)) e.symm).trans (pull_comp φ g.imageι _)
  have h₄ : interNumRed k ⟨Set.range g.imageι, g.imageι.isClosedEmbedding.isClosed_range⟩ ![L] =
      interNum k (structureModule g.image) ![L.pull g.imageι] :=
    (InterModel.interNumRed_eq_interNumOn k g.imageι _ rfl _).trans
      ((interNumOn_eq_interNum_pull (appTop_algebraΓOfHom g.imageι p rfl) (isLB_vecOne hL)).trans
        (congrArg _ (funext fun j => by fin_cases j; rfl)))
  rw [hdeg L hL, h₃, ← h₂, h₁, h₄]

end GlobalTheory.NumPull

namespace GlobalTheory.NumPull

theorem interNumRed_pull_proportional : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W), IsProjOver p → IsProjOver (f ≫ p) → letI := algebraΓOfHom p; letI := algebraΓOfHom (f ≫ p); ∀ (L L' : LB W), L.IsLB → L'.IsLB → ∀ (a b : ℕ), (∀ C : Closeds W, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L] = b * interNumRed ℂ C ![L']) → ∀ C : Closeds M, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L.pull f] = b * interNumRed ℂ C ![L'.pull f] := by
  intro M W _ _ p f hp _
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (f ≫ p)
  intro L L' hL hL' a b H C hC
  have : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  rcases interNumRed_pull_curve p f C hC with h | ⟨C', hC', d, hd⟩
  · rw [h L hL, h L' hL', mul_zero, mul_zero]
  · rw [hd L hL, hd L' hL']
    linear_combination (d : ℤ) * H C' hC'

end GlobalTheory.NumPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEigenvectorIntegralOfTangentPullbackMem
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanEigInt

theorem isEigV_of_tanPull_mem : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (x : Sp T.V ⟶ Y.X) (x' : Sp T.Fr ⟶ Y.X) (e : spMap (algebraMap T.V T.Fr) ≫ x = x'), Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) → ∀ (G : SAB H (Sp T.V)) (ψ : SABMap G Y.t x) (τ : E →+* ℂ) (w : epsOver T.V T.V ⟶ G.G) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ → GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e v ∈ GlobalTheory.FlagMod.eigLie c x' τ → IsEigV c io G τ w := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io x x' e hinj G ψ τ w v hv hmem a z hz
  have h1 : ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a v = z • v := by
    apply hinj
    rw [GlobalTheory.FlagMod.tanPull_actR, map_smulₛₗ, hmem a, hz]
    rfl
  have h2 : (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left ≫ (Y.t.act.act a).left =
      spMap (epsMul z) ≫ (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left :=
    congrArg (fun u => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv u).left) h1
  have hc : (epsMul z).comp ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) =
      (algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V) :=
    RingHom.ext fun r => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  apply ψ.cart.1.hom_ext
  · rw [Over.comp_left, Category.assoc, ψ.act a, ← Category.assoc, ← hv, h2, hv, Category.assoc]
  · rw [Over.comp_left, Category.assoc, Over.w, Over.w, Category.assoc, Over.w]
    show spMap _ = spMap (epsMul z) ≫ spMap _
    rw [spMap_comp', hc]

end GlobalTheory.TanEigInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackPrj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.BaseCh

variable {K K' : Type} [Field K] [Field K']

abbrev prj (x : KeyIn K) (f : K →+* K') : ((Over.pullback (spMap f)).obj x.P.A).left ⟶ x.P.A.left :=
  pullback.fst x.P.A.hom (spMap f)

theorem isGrpPullback_prj (x : KeyIn K) (f : K →+* K') :
    IsGrpPullback ((Over.pullback (spMap f)).obj x.P.A) x.P.A (spMap f) (prj x f) :=
  isGrpPullback_pullback x.P.A (spMap f)

def pol (x : KeyIn K) (f : K →+* K') : Out.PolAV (Sp K') :=
  { A := (Over.pullback (spMap f)).obj x.P.A
    isAb := Out.TLinPf.isAb_pullback (spMap f) x.P.A x.P.isAb
    g := x.P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (isGrpPullback_prj x f).1
      x.P.smoothDim
    L := x.P.L.pull (prj x f)
    isLB := pull_isLB x.P.isLB (prj x f)
    rigid := PolBaseChange.rigidified_pull (isGrpPullback_prj x f) x.P.rigid
    sym := PolBaseChange.sym_pull (isGrpPullback_prj x f) x.P.sym
    ample := relAmple_pull (isGrpPullback_prj x f).1 x.P.isLB (pull_isLB x.P.isLB (prj x f))
      ((isGen_iff _).1 (idIso_isGen (pull_isLB x.P.isLB (prj x f)))) ⊤ (isAffineOpen_top _) (fun _ => trivial) x.P.ample
    ktriv := kTriv_pull (isGrpPullback_prj x f) x.P.isLB (pull_isLB x.P.isLB (prj x f))
      ((isGen_iff _).1 (idIso_isGen (pull_isLB x.P.isLB (prj x f)))) x.P.ktriv }

theorem eSec_prj (x : KeyIn K) (f : K →+* K') : eSec (pol x f).A ≫ prj x f = spMap f ≫ eSec x.P.A :=
  PolBaseChange.eSec_comm (isGrpPullback_prj x f)

theorem exists_th (x : KeyIn K) (f : K →+* K') :
    ∃ s' : (pol x f).L.Sec, ∀ (Z : Scheme) (r : Z ⟶ (pol x f).A.left) (z : Z) (j : x.P.L.ι) (k : (pol x f).L.ι),
      prj x f (r z) ∈ x.P.L.U j → r z ∈ (pol x f).L.U k →
        gs (r ≫ prj x f) z (x.P.L.U j) (x.th.f j) = ↑(gw (idIso (pol x f).L) r z j k) * gs r z ((pol x f).L.U k) (s'.f k) :=
  sec_pull_down ((isGen_iff _).1 (idIso_isGen (pull_isLB x.P.isLB (prj x f)))) x.P.isLB (pull_isLB x.P.isLB (prj x f)) x.th

def th (x : KeyIn K) (f : K →+* K') : (pol x f).L.Sec := Classical.choose (exists_th x f)

theorem th_spec (x : KeyIn K) (f : K →+* K') (Z : Scheme) (r : Z ⟶ (pol x f).A.left) (z : Z) (j : x.P.L.ι)
    (k : (pol x f).L.ι) (hj : prj x f (r z) ∈ x.P.L.U j) (hk : r z ∈ (pol x f).L.U k) :
    gs (r ≫ prj x f) z (x.P.L.U j) (x.th.f j) = ↑(gw (idIso (pol x f).L) r z j k) * gs r z ((pol x f).L.U k) ((th x f).f k) :=
  Classical.choose_spec (exists_th x f) Z r z j k hj hk

def rig (x : KeyIn K) (f : K →+* K') : ((pol x f).L.pull (eSec (pol x f).A)).Gen :=
  rigPullOf (G' := (pol x f).A) (G := x.P.A) (prj x f) (spMap f) (eSec_prj x f) x.P.L x.rig

theorem rig_isGen (x : KeyIn K) (f : K →+* K') : (rig x f).IsGen :=
  Out.LBxP.isGen_pullAlong x.P.L (prj x f) (spMap f) (fun _ : PUnit => eSec x.P.A) (fun _ => 1)
    (fun _ => eSec (pol x f).A) (fun _ => eSec_prj x f) x.rig x.rig_gen

theorem vec_sq (x : KeyIn K) (f : K →+* K') (i : Fin x.P.g) :
    (spMap (Chart.dualMapR f) ≫ (x.v i).left) ≫ x.P.A.hom = (epsR K').hom ≫ spMap f := by
  rw [Category.assoc, Over.w]
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

def vec (x : KeyIn K) (f : K →+* K') (i : Fin x.P.g) : epsR K' ⟶ (pol x f).A :=
  Over.homMk ((isGrpPullback_prj x f).1.lift _ _ (vec_sq x f i)) ((isGrpPullback_prj x f).1.lift_snd _ _ _)

theorem vec_prj (x : KeyIn K) (f : K →+* K') (i : Fin x.P.g) :
    (vec x f i).left ≫ prj x f = spMap (Chart.dualMapR f) ≫ (x.v i).left :=
  (isGrpPullback_prj x f).1.lift_fst _ _ _

theorem th_ne (x : KeyIn K) (f : K →+* K') (s : Sp K') :
    ∃ y, (pol x f).A.hom y = s ∧ y ∈ nonzeroLocus (th x f) := by
  have h := isGrpPullback_prj x f
  obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
  refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
  have u₁ : IsUnit (gs (prj x f) y _ (x.th.f k)) := by rw [gs_stalkMap (prj x f) y _ hk]; exact u.map _
  have e := th_spec x f _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
  erw [Category.id_comp] at e
  exact isUnit_of_mul_isUnit_right (e ▸ u₁)

def key (x : KeyIn K) (f : K →+* K') : KeyIn K' :=
  ⟨pol x f, x.g_pos, rig x f, rig_isGen x f, th x f, th_ne x f, vec x f,
    by have := x.P.isAb.smooth; exact Chart.isLieBasis_baseChange f (isGrpPullback_prj x f) x.basis (vec_prj x f)⟩

theorem powIso_le {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (n : ℕ)
    (p : (LB.div (lbPow (L.pull φ) n) ((lbPow L n).pull φ)).ι) :
    (LB.div (lbPow (L.pull φ) n) ((lbPow L n).pull φ)).U p ≤
      φ ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p.2 PUnit.unit PUnit.unit)) := by
  intro y hy
  obtain ⟨h1, h2⟩ := hy
  have a1 := Set.mem_iInter.1 (Set.mem_iInter.1 h1 PUnit.unit) PUnit.unit
  have a2 := Set.mem_iInter.1 (Set.mem_iInter.1 h2 PUnit.unit) PUnit.unit
  exact ⟨a1, a2⟩

def powIso {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (n : ℕ) : LB.Iso ((lbPow L n).pull φ) (lbPow (L.pull φ) n) :=
  ⟨fun p => res (powIso_le L φ n p)
      (pullU φ _ (L.g (p.1 PUnit.unit PUnit.unit) (p.2 PUnit.unit PUnit.unit))) ^ (n : ℤ)⟩

end GlobalTheory.MBLow.BaseCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralFourierCoeffClassIndicatorLevelPoint
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovInt

open IsDedekindDomain

def intZ (D : D7) {H : Host D.host.E} (Dw : Datum H) (l : Level H) (n : ℕ) (w : (D.host.E →+* ℂ) × ℕ → ℕ) : ℕ :=
  Nat.card (Fin n → LevQ Dw l) * (NumberField.discr D.host.E).natAbs ^ Formalism.L2.Pj.DF Dw w *
    l.M ^ Formalism.L2.Pj.DF Dw w

theorem intZ_eq (D : D7) {H : Host D.host.E} (Dw : Datum H) (l : Level H) (n : ℕ) (w : (D.host.E →+* ℂ) × ℕ → ℕ) :
    intZ D Dw l n w = l.M ^ (Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) * n) *
      (NumberField.discr D.host.E).natAbs ^ Formalism.L2.Pj.DF Dw w * l.M ^ Formalism.L2.Pj.DF Dw w := by
  rw [intZ, GlobalTheory.PlaceInt.card_fun_levQ]

theorem sum_padicValNat_mul_le (v : ℕ → ℤ) (hv : ∀ a b, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b) (h0 : ∀ a, 0 ≤ v a)
    {N : ℕ} (hN : N ≠ 0) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, (padicValNat p N : ℤ) * v p ≤ v N := by
  classical
  have h1 : v 1 = 0 := by have := hv 1 1 one_ne_zero one_ne_zero; rw [Nat.mul_one] at this; omega
  have key : ∀ N : ℕ, N ≠ 0 → ∑ p ∈ s, (padicValNat p N : ℤ) * v p ≤ v N := by
    intro N
    induction N using Nat.recOnMul with
    | zero => exact fun h => absurd rfl h
    | one => intro _; simp [h1]
    | prime l hl =>
      intro _
      have : ∀ p ∈ s, (padicValNat p l : ℤ) * v p = if p = l then v l else 0 := by
        intro p hp
        haveI := Fact.mk (hs p hp)
        haveI := Fact.mk hl
        split_ifs with h
        · subst h; simp
        · rw [padicValNat_primes h]; simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      split_ifs
      exacts [le_rfl, h0 _]
    | mul a b iha ihb =>
      intro hab
      have ha := left_ne_zero_of_mul hab
      have hb := right_ne_zero_of_mul hab
      have : ∀ p ∈ s, (padicValNat p (a * b) : ℤ) * v p = (padicValNat p a : ℤ) * v p + (padicValNat p b : ℤ) * v p := by
        intro p hp
        haveI := Fact.mk (hs p hp)
        rw [padicValNat.mul ha hb]; push_cast; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hv a b ha hb]
      exact add_le_add (iha ha) (ihb hb)
  exact key N hN

theorem ram_sum_le_vV_discr (E : Type) [Field E] [NumberField E] (T : CDVR) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (e X : ℕ) :
    ∑ p ∈ s, (vV T.V (p : T.Fr) : ℝ) / e *
        ((padicValNat p (NumberField.discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ)) * (X : ℝ) / 2 ≤
      (vV T.V (((NumberField.discr E).natAbs ^ X : ℕ) : T.Fr) : ℝ) / e := by
  haveI : CharZero T.Fr := algebraRat.charZero _
  have hN : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
  have h0 : ∀ a : ℕ, 0 ≤ vV T.V (a : T.Fr) := fun a => GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T a
  have h1 := sum_padicValNat_mul_le (fun a => vV T.V (a : T.Fr))
    (fun a b ha hb => by
      simp only [Nat.cast_mul]
      exact vV_mul (Nat.cast_ne_zero.2 ha) (Nat.cast_ne_zero.2 hb)) h0 hN s hs
  have h2 : ∑ p ∈ s, (padicValNat p (NumberField.discr E).natAbs : ℝ) * (vV T.V (p : T.Fr) : ℝ) ≤
      (vV T.V (((NumberField.discr E).natAbs : ℕ) : T.Fr) : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).2 h1
    rw [Int.cast_sum] at h
    simpa only [Int.cast_mul, Int.cast_natCast] using h
  have hk : (1 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E))
  rw [Nat.cast_pow, GlobalTheory.ShortBound.vV_pow (Nat.cast_ne_zero.2 hN), Int.cast_mul, Int.cast_natCast]
  have hX : (0 : ℝ) ≤ (X : ℝ) / e := by positivity
  refine le_trans ?_ ((mul_le_mul_of_nonneg_left h2 hX).trans (le_of_eq (by ring)))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have h3 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast h0 p
  have h4 : (padicValNat p (NumberField.discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ) ≤
      (padicValNat p (NumberField.discr E).natAbs : ℝ) := div_le_self (Nat.cast_nonneg _) hk
  have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hX h3)
  have h6 : (0 : ℝ) ≤ (X : ℝ) / e * (vV T.V (p : T.Fr) : ℝ) * (padicValNat p (NumberField.discr E).natAbs : ℝ) :=
    mul_nonneg (mul_nonneg hX h3) (Nat.cast_nonneg _)
  calc _ = (X : ℝ) / e * (vV T.V (p : T.Fr) : ℝ) *
        ((padicValNat p (NumberField.discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ)) / 2 := by ring
    _ ≤ (X : ℝ) / e * (vV T.V (p : T.Fr) : ℝ) * (padicValNat p (NumberField.discr E).natAbs : ℝ) := by linarith
    _ = _ := by ring

theorem log_discr_natAbs_le (E : Type) [Field E] [NumberField E] :
    Real.log ((NumberField.discr E).natAbs : ℝ) ≤ (Module.finrank ℚ E : ℝ) * fieldSz E := by
  have hk : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E))
  have h := (div_le_iff₀ hk).1 (log_rd_le_fieldSz E)
  rw [Nat.cast_natAbs, Int.cast_abs]
  linarith

theorem isIntegral_fourierCoeff_classIndicator_levelPoint {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) (hM : l.M ≠ 0) {n : ℕ} (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw l) : IsIntegral ℤ (x0Dat c x0 q) := by
  unfold x0Dat
  refine ⟨Polynomial.X ^ l.M - 1, Polynomial.monic_X_pow_sub_C 1 hM, ?_⟩
  have h1 : zetaM c ^ l.M = 1 := GlobalTheory.Survey.BaseClassMove.zetaM_pow c
  have h2 : (zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b))) ^ l.M = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
  simp [h2]

end GlobalTheory.CovInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmoothProjectiveModificationOfNonempty
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

namespace GlobalTheory

theorem isIntegral_of_nonempty_modif : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (U : Y.Opens) (d : ℕ)
    (M : Modif p U d), (U : Set Y).Nonempty → IsIntegral M.X := by
  intro F _ Y _ p U d M hU
  have hUi : IsIrreducible (U : Set Y) :=
    ⟨hU, (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset U.isOpen (Set.subset_univ _)⟩
  have := M.iso
  let g : (U : Scheme) ⟶ M.X := inv (M.σ ∣_ U) ≫ (M.σ ⁻¹ᵁ U).ι
  have hrange : Set.range g.base = ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X) := by
    have hs : Function.Surjective (inv (M.σ ∣_ U)).base := (inv (M.σ ∣_ U)).surjective
    simp only [g, Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp, hs.range_eq,
      Set.image_univ]
    exact Scheme.Opens.range_ι _
  have hopn : IsIrreducible ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X) := by
    rw [← hrange, ← Set.image_univ]
    have : IrreducibleSpace (U : Scheme) := Subtype.irreducibleSpace hUi
    exact (IrreducibleSpace.isIrreducible_univ (U : Scheme)).image _ g.base.hom.continuous.continuousOn
  have hcl : IsIrreducible (Set.univ : Set M.X) := by
    rw [← M.dense.closure_eq]; exact hopn.closure
  have : IrreducibleSpace M.X := irreducibleSpace_def _ |>.mpr hcl
  have : Smooth M.str := SmoothOfRelativeDimension.smooth d _
  exact isIntegral_of_smooth_field M.str

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedInFibreOfEtaleRestriction
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

namespace GlobalTheory

theorem isolated_in_fibre_of_etale_restrict :
    ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : W.Opens), Etale (f ∣_ U) → ∀ z : M, f z ∈ U →
      ∃ V : M.Opens, z ∈ V ∧ ∀ y ∈ V, f y = f z → y = z := by
  intro M W f U hE z hz
  haveI : LocallyQuasiFinite (f ∣_ U) := by
    refine ⟨fun {U'} hU {V} hV e => ?_⟩
    have h := Scheme.Hom.etale_appLE (f ∣_ U) hU hV e
    algebraize [((f ∣_ U).appLE U' V e).hom]
    exact RingHom.quasiFinite_algebraMap.mpr inferInstance
  let z' : (f ⁻¹ᵁ U : M.Opens) := ⟨z, hz⟩
  obtain ⟨u, hu, huz⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    ((f ∣_ U).isDiscrete_preimage_singleton ((f ∣_ U) z')) z' rfl
  refine ⟨⟨Subtype.val '' u, (f ⁻¹ᵁ U).isOpen.isOpenMap_subtype_val u hu⟩, ⟨z', ?_, rfl⟩, ?_⟩
  · have : z' ∈ u ∩ (f ∣_ U) ⁻¹' {(f ∣_ U) z'} := by rw [huz]; rfl
    exact this.1
  · rintro y ⟨y', hy'u, rfl⟩ hy
    have hmem : y' ∈ u ∩ (f ∣_ U) ⁻¹' {(f ∣_ U) z'} := by
      refine ⟨hy'u, ?_⟩
      have h1 := morphismRestrict_base_coe f U y'
      have h2 := morphismRestrict_base_coe f U z'
      exact Subtype.ext (h1.trans (hy.trans h2.symm))
    rw [huz] at hmem
    exact congrArg Subtype.val hmem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeCommRingStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_commRing : GlobalTheory.Published.AbelianDeRham → ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {g : ℕ}, Semi.IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  first | exact @GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring | exact GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring | (intros; apply GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring <;> assumption)
end

