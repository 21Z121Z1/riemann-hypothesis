import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3591
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0223
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2969
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3596
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2909

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapStalkHomFromSpecStalk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_stalkHom_fromSpecStalk {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) :
    spMap (M.stalkHom z) ≫ M.Z.fromSpecStalk z = M.pt := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (M.pt_specializes (IsLocalRing.closedPoint Ω) z)
  refine Eq.trans ?_ h1
  rw [← h2, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem exists_uMem_injective : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X), Function.Injective ev ∧ Nonempty (UMem X₁ z₁ act V ev X t δ) := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hth X₁ z₁ act hact
  obtain ⟨hdom, hfr, hic, hnoeth⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI : CharZero (X₁.M.Z.presheaf.stalk z₁) := (X₁.M.stalkHom z₁).charZero
  obtain ⟨V₀, _, _, _, φ₀, ⟨hdvr, hcpl, hchar⟩, hinj₀, hmax⟩ :=
    GlobalTheory.ClosedPol.exists_cdvr (X₁.M.Z.presheaf.stalk z₁) (maximalIdeal _)
  haveI : IsLocalHom φ₀ := ((IsLocalRing.local_hom_TFAE φ₀).out 0 4).2 hmax
  have hB : GlobalTheory.Mum.Base V₀ := ⟨⟨inferInstance, inferInstance, inferInstance, hcpl⟩, hchar⟩
  have hg₀ : Function.Injective ((algebraMap V₀ (FractionRing V₀)).comp φ₀) :=
    (IsFractionRing.injective V₀ (FractionRing V₀)).comp hinj₀
  let emb : X₁.Ω₁ →+* FractionRing V₀ := IsFractionRing.lift (A := X₁.M.Z.presheaf.stalk z₁) hg₀
  have hemb : ∀ r, emb (X₁.M.stalkHom z₁ r) = algebraMap V₀ (FractionRing V₀) (φ₀ r) := fun r =>
    IsFractionRing.lift_algebraMap (A := X₁.M.Z.presheaf.stalk z₁) hg₀ r
  have hpt : jK V₀ ≫ spMap φ₀ ≫ X₁.M.Z.fromSpecStalk z₁ = spMap emb ≫ X₁.M.pt := by
    rw [← spMap_stalkHom_fromSpecStalk, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_comp_spMap, spMap_comp_spMap]
    congr 1
    ext r
    exact (hemb r).symm
  let y₀ : Sp (FractionRing V₀) ⟶ F.X := spMap emb ≫ spMap X₁.S.R.val.toRingHom ≫ X₁.u
  have hy₀ : y₀ ≫ i = jK V₀ ≫ spMap φ₀ ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π := by
    simp only [y₀, Category.assoc]
    rw [← X₁.comp, ← Category.assoc (jK V₀), ← Category.assoc (jK V₀ ≫ spMap φ₀), Category.assoc (jK V₀), hpt,
      Category.assoc]
  obtain ⟨T, f, fK, hf, hfl, hff, hfK, hTy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ (zetaAway n) F V₀ hB hdvr y₀
  haveI := hfl
  let ev : X₁.M.Z.presheaf.stalk z₁ →+* T.V := f.comp φ₀
  have hev : Function.Injective ev := hf.comp hinj₀
  have hkey : jK T.V ≫ spMap ev = spMap fK ≫ jK V₀ ≫ spMap φ₀ := by
    rw [show jK T.V = spMap (algebraMap T.V (FractionRing T.V)) from rfl,
      show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_comp_spMap, spMap_comp_spMap,
      spMap_comp_spMap]
    congr 1
    ext a
    simp only [RingHom.comp_apply]
    exact (hfK _).symm
  have hpt' : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ = spMap fK ≫ spMap emb ≫ X₁.M.pt := by
    rw [← Category.assoc, hkey, Category.assoc, Category.assoc, hpt]
  have hreg : RegAt X₁ z₁ ev := by
    intro a _
    rw [hpt']
    change a ∈ X₁.M.O (X₁.M.pt ((spMap fK ≫ spMap emb) (closedPoint (FractionRing T.V))))
    rw [X₁.M.pt_apply, RatModel.O_genericPoint]
    trivial
  have hcomm : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i := by
    rw [hTy, Category.assoc, hy₀, ← Category.assoc (jK T.V), hkey]
    simp only [Category.assoc]
  obtain ⟨hmono, hnn, -, -⟩ := GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef g n _ (zetaAway n) F T
  have hCN : IsCN T.V := ⟨inferInstance, inferInstance, T.complete, inferInstance⟩
  obtain ⟨𝔪, -⟩ := GlobalTheory.T.exists_uniformised_member_of_refined_uniformisation g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth X₁ z₁ act hact T.V
    (Wit.ofDeg T.D.toPre T.D.tau_bimult) 1 ![T.ϖ] ![T.β] (fun k => by fin_cases k; exact T.irr.ne_zero)
    (fun k a b => by fin_cases k; exact T.symm a b) (fun k a => by fin_cases k; exact hnn a) hmono T.V (RingHom.id _)
    hCN Function.injective_id (RingHom.Finite.id T.V) T.D (AddEquiv.refl _) (Wit.refines_ofDeg _ _) T.G T.A T.U T.y T.α T.α₂
    T.semi T.cart T.sq T.lb ev inferInstance hreg hcomm
  exact ⟨T.V, inferInstance, inferInstance, inferInstance, ev, _, inferInstance, 1, _, _, hev, ⟨𝔪⟩⟩
end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerFrameCompat
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
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageUniq

open GlobalTheory.SquareComm GlobalTheory.BotUniq

private theorem gBig_mono {P Q : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨CF1, h1⟩ := hP
  refine ⟨CF1, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF hCF
  exact ⟨C1, x1, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (g1 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩

private theorem uniq_of_triple_inf (hH : GlobalTheory.Published.HoweDualityReal) (hP : GlobalTheory.FunPr.Hypotheses₂) (hL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) {A A' WW : HSp D} (α β : (AE D)ˣ →* Circle)
    (hT : IsTriple A A' WW α β) (m : MeasureTheory.Measure (GA D A)) (fd : Set (GA D A))
    (m' : MeasureTheory.Measure (GA D A')) (fd' : Set (GA D A'))
    (hme : IsHaarFD A m fd) (hme' : IsHaarFD A' m' fd') (ω : GlobalTheory.Grid.WRep A WW) (ω' : GlobalTheory.Grid.WRep A' WW)
    (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW)
    (Pi₀ : ModuleCat.{0} ℂ) (rf₀ : GA D WW → Module.End ℂ Pi₀)
    (rl₀ : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi₀)
    (p₀ : (WO A WW → ℂ) →ₗ[ℂ] Pi₀) (p₀' : (WO A' WW → ℂ) →ₗ[ℂ] Pi₀)
    (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi)
    (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi)
    (hm₀ : IsMatch ψ θ FA FA' FW α β ω ω' Pi₀ rf₀ rl₀ p₀ p₀')
    (hm : IsMatch ψ θ FA FA' FW α β ω ω' Pi rf rl p p') :
    ∃ (E : Pi₀ ≃ₗ[ℂ] Pi) (c : ℂ), c ≠ 0 ∧ (∀ Φ ∈ algF ψ θ true FA FW, p Φ = c • E (p₀ Φ)) ∧
      ∀ Φ' ∈ algF ψ θ false FA' FW, p' Φ' = E (p₀' Φ') := by
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ := GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ A A' WW FA FA' FW _ _ hT m fd m' fd'
    hme hme' ω ω' hm.weilA hm.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs A.rank A'.rank Γ Xc om om' hTD
  have kA : ∀ Φ ∈ algF ψ θ true FA FW, p₀ Φ = 0 ↔ p Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algA Φ hΦ
    rw [GlobalTheory.SquareAgree.ker_p_iff_polMatch_zero hP.howeDualityUnitary hH hP.minguezThetaGL hP D _ _ A A' WW FA FA' FW _ _ _ _
        _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀ Φ hΦ ΦD hΦD hD,
      GlobalTheory.SquareAgree.ker_p_iff_polMatch_zero hP.howeDualityUnitary hH hP.minguezThetaGL hP D _ _ A A' WW FA FA' FW _ _ _ _
        _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hm Φ hΦ ΦD hΦD hD]
  have kB : ∀ Φ ∈ algF ψ θ false FA' FW, p₀' Φ = 0 ↔ p' Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algB Φ hΦ
    rw [GlobalTheory.SquareAgree.pPrime_eq_zero_iff_polMatch hP.howeDualityUnitary hH hP.minguezThetaGL hP D _ _ A A' WW FA FA' FW _ _
        _ _ _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀ Φ hΦ ΦD hΦD hD,
      GlobalTheory.SquareAgree.pPrime_eq_zero_iff_polMatch hP.howeDualityUnitary hH hP.minguezThetaGL hP D _ _ A A' WW FA FA' FW _ _
        _ _ _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hm Φ hΦ ΦD hΦD hD]
  obtain ⟨EA, hEA⟩ := exists_equiv_of_ker _ p₀ p hm₀.mapA.onto hm.mapA.onto kA
  obtain ⟨EB, hEB⟩ := exists_equiv_of_ker _ p₀' p' hm₀.mapB.onto hm.mapB.onto kB
  have fA : ∀ h ∈ GfC WW, ∀ x, EA (rf₀ h x) = rf h (EA x) := fun h hh =>
    intertwine _ p₀ p EA hEA hm₀.mapA.onto _ _ fun Φ hΦ =>
      ⟨_, hm₀.mapA.stabX.1 h hh Φ hΦ, hm₀.mapA.eqf h hh Φ hΦ, hm.mapA.eqf h hh Φ hΦ⟩
  have fB : ∀ h ∈ GfC WW, ∀ x, EB (rf₀ h x) = rf h (EB x) := fun h hh =>
    intertwine _ p₀' p' EB hEB hm₀.mapB.onto _ _ fun Φ hΦ =>
      ⟨_, hm₀.mapB.stabX.1 h hh Φ hΦ, hm₀.mapB.eqf h hh Φ hΦ, hm.mapB.eqf h hh Φ hΦ⟩
  have lA : ∀ τ, ∀ Y ∈ lieAt WW τ, ∀ x, EA (rl₀ τ Y x) = rl τ Y (EA x) := fun τ Y hY =>
    intertwine _ p₀ p EA hEA hm₀.mapA.onto _ _ fun Φ hΦ => by
      obtain ⟨Φ', hΦ', hd⟩ := hm₀.mapA.stabX.2 τ Y hY Φ hΦ
      exact ⟨Φ', hΦ', hm₀.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd, hm.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd⟩
  have lB : ∀ τ, ∀ Y ∈ lieAt WW τ, ∀ x, EB (rl₀ τ Y x) = rl τ Y (EB x) := fun τ Y hY =>
    intertwine _ p₀' p' EB hEB hm₀.mapB.onto _ _ fun Φ hΦ => by
      obtain ⟨Φ', hΦ', hd⟩ := hm₀.mapB.stabX.2 τ Y hY Φ hΦ
      exact ⟨Φ', hΦ', hm₀.mapB.eql τ Y hY Φ hΦ Φ' hΦ' hd, hm.mapB.eql τ Y hY Φ hΦ Φ' hΦ' hd⟩
  let ι := {g // g ∈ GfC WW} ⊕ {x : D.what₂.Tau × Matrix (Fin WW.rank) (Fin WW.rank) ℂ // x.2 ∈ lieAt WW x.1}
  let ρ : ι → Module.End ℂ Pi₀ := Sum.elim (fun g => rf₀ g.1) (fun x => rl₀ x.1.1 x.1.2)
  have hrank : Module.rank ℂ Pi₀ ≤ Cardinal.aleph0 :=
    GlobalTheory.SquareAgree.rank_pi_le_aleph0 hP.howeDualityUnitary hH hP D _ _ A A' WW FA FA' FW _ _ _ _ _ _ _ _ e Bs Γ Xc om om'
      cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀
  have hirr : ∀ N : Submodule ℂ Pi₀, (∀ k, ∀ x ∈ N, ρ k x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN =>
    hm₀.irred.2 N (fun g hg x hx => hN (Sum.inl ⟨g, hg⟩) x hx) fun τ Y hY x hx => hN (Sum.inr ⟨(τ, Y), hY⟩) x hx
  have hcomm : ∀ k, ((EA.trans EB.symm : Pi₀ ≃ₗ[ℂ] Pi₀) : Module.End ℂ Pi₀) * ρ k =
      ρ k * ((EA.trans EB.symm : Pi₀ ≃ₗ[ℂ] Pi₀) : Module.End ℂ Pi₀) := by
    rintro (⟨g, hg⟩ | ⟨⟨τ, Y⟩, hY⟩)
    · exact comm_of_intertwine EA EB _ _ (fA g hg) (fB g hg)
    · exact comm_of_intertwine EA EB _ _ (lA τ Y hY) (lB τ Y hY)
  obtain ⟨c, hc⟩ := GlobalTheory.dixmier_commutant_scalar ι Pi₀ ρ hrank hirr _ hcomm
  have hT' : ∀ x, EB.symm (EA x) = c • x := fun x => by
    have := LinearMap.congr_fun hc x
    simpa using this
  haveI : Nontrivial Pi₀ := hm₀.irred.1
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : Pi₀)
    have h1 := hT' x
    rw [zero_smul, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at h1
    exact hx h1
  refine ⟨EB, c, hc0, fun Φ hΦ => ?_, fun Φ hΦ => hEB Φ hΦ⟩
  rw [hEA Φ hΦ, ← LinearEquiv.map_smul, ← hT', LinearEquiv.apply_symm_apply]

theorem _root_.GlobalTheory.T.square_tower_frame_compat : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (a b : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j a b X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), ∀ (Pi₀ : ModuleCat.{0} ℂ) rf₀ rl₀ p₀ p₀' (Pi : ModuleCat.{0} ℂ) rf rl p p',
    GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi₀ rf₀ rl₀ p₀ p₀' →
    GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∃ (E : Pi₀ ≃ₗ[ℂ] Pi) (c : ℂ), c ≠ 0 ∧ (∀ Φ ∈ GlobalTheory.SquareComm.algF W.ψ W.θ true FA FW, p Φ = c • E (p₀ Φ)) ∧
      ∀ Φ' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW, p' Φ' = E (p₀' Φ') := by
  intro hP _ hL
  refine gBig_mono GlobalTheory.T.towerStage_seesawDictionary_framesSignatures ?_
  intro D T Lc sc G μ₀ C x b _ H W i j a a' A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  obtain ⟨_, _, _, _, _, -, -, -, hall⟩ := H W i j a a' A A' WW X hX
  have hIs := hX.2.2.2.2.2.2.2
  exact uniq_of_triple_inf hP.howeDualityReal hP hL W.ψ W.θ hIs.isVac.2.inf _ _ (hall t).1 X.m X.fd X.m' X.fd'
    hIs.meas hIs.meas' (X.ω t) (X.ω' t) FA FA' FW Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm

end GlobalTheory.StageUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesSharpReferenceSixteenTerms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharp_fibre_iso_exists : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∃ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f ∧ LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) ∧ (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) := by
  intro g l hl hodd W hW
  have LL := GlobalTheory.abelianSchemeLaws_all
  choose J hJ Mat κ w w' hTf using GlobalTheory.T.fibre_eighth_power_theta_object_subfield W hW
  have hD := fun gQ : ℕ => @GlobalTheory.T.descend_to_thetaConstant_field LL.1 LL.2 (8 * gQ) (J gQ) (hJ gQ) (Mat gQ) (κ gQ) l (w gQ) (w' gQ) hl hodd
  choose j₀f hj₀f using hD
  refine ⟨(Finset.range (g + 1)).sup j₀f + 1, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hS C u mo hmo hTh K _ _ ev k₀ hk₀ hrat σ hσ
  have hj1 : 1 ≤ j := by omega
  obtain ⟨bT, t, v, ψ, hSh, hPr, hHT, hψ, hL, htor⟩ :=
    hTf Q.g l hl hodd j hj1 V V₁ hCN hlu Q rfl ρ hρ D e hS C u mo hmo hTh K ev k₀ hk₀ hrat
  have hle : j₀f Q.g ≤ j := by
    have := Finset.le_sup (f := j₀f) (Finset.mem_range.2 (by omega : Q.g < g + 1))
    omega
  have hs : spMap k₀.subtype = spMap k₀.subtype ≫ spMap (RingHom.id k₀) := by
    simp [spMap]
  obtain ⟨t₀, ⟨φ, hφ, hLφ, hpts, -⟩, -⟩ :=
    hj₀f Q.g j hle k₀ bT k₀ K (RingHom.id k₀) k₀.subtype (spMap k₀.subtype) t v hs hSh hPr hHT
  have hσe : σ.toRingHom.comp k₀.subtype = k₀.subtype := RingHom.ext fun r => hσ r r.2
  obtain ⟨f, hf, hfL, hfq⟩ := GlobalTheory.Poinc.Sep.Twist.twist_fibre_iso V₁ D.P.A D.P.L D.P.isLB K ev σ k₀ k₀.subtype hσe t.A t.L t.isLB ψ hψ hL t₀.A t₀.L t₀.isLB φ hφ hLφ
  refine ⟨f, hf, hfL, ?_⟩
  intro y hy q hq1 hq2
  obtain ⟨k, hk⟩ := hy
  obtain ⟨y', hy'1, hy'2⟩ := GlobalTheory.T.torsion_fibre_point_transfer_fixed_model V₁ D.P.A K ev t.A ψ hψ k₀ k₀.subtype t₀.A φ hφ (l ^ k) y hk q hq1 hq2
  haveI : IsAlgClosed k₀ := hk₀
  have hlk : IsUnit ((l ^ k : ℕ) : k₀) := by
    have h1 : IsUnit (ev (l : V₁)) := hlu.map ev
    have h2 : IsUnit ((l : k₀) : K) := by simpa using h1
    have h3 : IsUnit (l : k₀) := by
      rcases h2.exists_left_inv with ⟨x, hx⟩
      exact isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hx
    simpa using h3.pow k
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.abelianScheme_primeToChar_torsion_rational k₀ K k₀.subtype t₀.A t₀.ab (l ^ k) hlk y' hy'1
  rw [hfq q y₀ (by rw [← hy'2, hy₀]) hq2, hq1]

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTermCoefficientSqEqMonomialSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTerm_coefficient_sq_eq_monomial_subfield : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.PsiEven → D.TauBimult → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (τ₀ : GlobalTheory.UChart.Gens D) (m N : ℕ) (s : Fin m ⊕ Fin N → V₁) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ D.X), (∀ k, IsUnit (s (.inr k))) → GlobalTheory.UChart.TauIn D τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → (∀ mu, algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 = ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inl k)) ^ ε (.inl k) (e mu) (e mu)) → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁), GlobalTheory.UChart.FromBase D τ₀ ib → (∀ a, ev (ib a) ∈ k₀) → ∀ mu c, ∃ r ∈ k₀, ev (u mu c) ^ 2 = r * ∏ k, ev (s (.inr k)) ^ ε (.inr k) (e mu) (e mu) := by
  first | exact @GlobalTheory.USep.Coef.coef_sq_mem_monomial | exact GlobalTheory.USep.Coef.coef_sq_mem_monomial | (intros; apply GlobalTheory.USep.Coef.coef_sq_mem_monomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsAffineTwoMembers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.Poinc.Sep

theorem sumF_comp_equiv {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {K : Type} [Field K]
    [Algebra (FractionRing R) K] {Ix Jx : Type} {x : Ix → K} {s : K} (e : Jx ≃ Ix) (h : SumF I K x s) :
    SumF I K (fun j => x (e j)) s := by
  letI : Module R K := Module.compHom K (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, hlim⟩ := h
  refine ⟨N, hN, hs, fun j => hx _, fun k => ?_⟩
  classical
  obtain ⟨S, hS⟩ := hlim k
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have hsub : S ⊆ T.map e.toEmbedding := by
    intro a ha
    have := hT (Finset.mem_map_of_mem e.symm.toEmbedding ha)
    exact Finset.mem_map.2 ⟨e.symm a, this, by simp⟩
  have := hS _ hsub
  rwa [Finset.sum_map] at this

theorem sum_terms : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T → ∀ (c : C), SumF (maximalIdeal V) (FractionRing V) (fun mu : Fin 8 → X => algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem (lab c)⟩) := by
  intro g n F W Z i X₁ z₁ act x₀ _ V _ _ _ ev X _ m t δ 𝔪 C lab T hT c
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hexp, hg', hTe⟩ := hT
  have hO := (hg' c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hg' c).2.1 th s _ hexp (hth (lab c))
  have := sumF_comp_equiv 𝔪.e₈.toEquiv hO
  convert this using 1
  funext mu
  exact hTe mu c

theorem twistSum_of_transExp {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {x₀ : X₁.S.Gam} (hd : X₁.M.Div X₁.S.th x₀ z₁) (sg : ℤˣ)
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ)
    (hW : ∀ (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), TorChar 𝔪 τ χ →
      ∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) =
        𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))
    {C : Type} (lab : C → X₁.S.Gam) (hlab : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁) (T : (Fin 8 → X) → C → V)
    (hT : 𝔪.Terms x₀ lab T) (c : C) (τ : X₁.S.Gam) (hτ : τ ∈ X₁.S.TT X₁.M z₁) (e : ℕ)
    (hE : TransExp 𝔪 x₀ (lab c) τ e) : TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  obtain ⟨χ, hχ1, hχ2⟩ := GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ hτ
  obtain ⟨T', hT'⟩ := GlobalTheory.T.exists_thetaTerms_torusTranslate g n F W Z i X₁ z₁ act x₀ hd V ev X m t δ 𝔪 C lab hlab T hT c τ hτ
  have hprop := hE χ ⟨hχ1, hχ2⟩ C lab T hT c rfl Unit _ T' hT' () rfl
  have hsum := sumF_const_mul (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)))
    (sum_terms g n F W Z i X₁ z₁ act x₀ hd V ev X m t δ 𝔪 Unit (fun _ => lab c + τ) T' hT' ())
  refine GlobalTheory.Poinc.TwistSum₂.twistSum_of_sumF g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ C lab T sg c τ χ e
    (UMem.yK_th_ne_zero g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hd)
    (UMem.exists_yy g n F W Z i X₁ z₁ act V ev X m t δ 𝔪) (hW τ χ ⟨hχ1, hχ2⟩) ?_
  convert hsum using 1
  funext mu
  rw [← _root_.mul_assoc, hprop mu, _root_.mul_assoc]

theorem twistSum_exp_affine : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (m2 : ℕ) (t2 : Fin m2 → V2) (δ2 : Fin m2 → LinearMap.BilinForm ℤ Y2) (𝔪2 : UMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∃ ε1 ε2 : X₁.S.Gam → X₁.S.Gam → ℕ, (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ (ε1 (lab c) τ)) ∧ (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y2) → C → V2, 𝔪2.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, TwistSum X₁ z₁ act x₀ 𝔪2 lab T sg c τ (ε2 (lab c) τ)) ∧ ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((ε1 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((ε2 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  intro g n F W Z i X₁ z₁ act x₀ hd sg _ hW V1 _ _ _ ev1 Y1 _ m1 t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ m2 t2 δ2 𝔪2
  classical
  have hA := GlobalTheory.T.thetaSetup_translation_exponents_affine g n F W Z i X₁ z₁ act x₀ hd V1 ev1 Y1 m1 t1 δ1 𝔪1 V2 ev2 Y2 m2 t2 δ2 𝔪2
  choose! F1 F2 hF1 hF2 hAff using hA
  refine ⟨fun a τ => F1 τ a, fun a τ => F2 τ a, ?_, ?_, fun τ hτ => hAff τ hτ⟩
  · intro C lab hlab T hT c τ hτ
    exact twistSum_of_transExp hd sg 𝔪1 (fun τ χ hχ => hW V1 ev1 Y1 m1 t1 δ1 𝔪1 τ χ hχ.1 hχ.2) lab hlab T hT c τ hτ _
      (hF1 τ hτ (lab c) (hlab c))
  · intro C lab hlab T hT c τ hτ
    exact twistSum_of_transExp hd sg 𝔪2 (fun τ χ hχ => hW V2 ev2 Y2 m2 t2 δ2 𝔪2 τ χ hχ.1 hχ.2) lab hlab T hT c τ hτ _
      (hF2 τ hτ (lab c) (hlab c))

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaPowerResidueDividingLabel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.Poinc.Sep.TwistResid

theorem twist_resid : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), lab c ∈ X₁.S.supI X₁.M z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ (sg : ℤˣ) (e : ℕ), TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ e → ∀ s u : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) → X₁.M.stalkHom z₁ u = X₁.S.th (lab c + τ) / X₁.S.th (lab c) → ev1 (s * u) - 1 ∈ maximalIdeal V1 := by
  classical
  intro g n F W Z i X₁ z₁ act x₀ hx₀ V _ _ _ ev Y _ m t δ 𝔪 C lab hlab T hT c hc τ hτ sg e hTw s u hs hu
  have hcd : X₁.M.Div X₁.S.th (lab c) z₁ := hc
  have hqO : X₁.S.th (lab c) / X₁.S.th x₀ ∈ X₁.M.O z₁ := hx₀.2 (lab c)
  let r := (X₁.M.stalkEquiv z₁).symm ⟨_, hqO⟩
  have hr : X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ := by
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  have hrU : IsUnit r := ((RatModel.isUnit_O_iff (⟨_, hqO⟩ : X₁.M.O z₁)).2
    ⟨div_ne_zero hcd.1 hx₀.1, by rw [inv_div]; exact hcd.2 x₀⟩).map (X₁.M.stalkEquiv z₁).symm
  obtain ⟨zt, hzt⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))
  obtain ⟨wt, hwt⟩ := GlobalTheory.T.twistWeight_wellDefined_on_lattice_class g n F W Z i X₁ z₁ act x₀ hx₀ V ev Y m t δ 𝔪 sg τ hτ
  let wt' : (Fin 8 → Y) → ZMod (X₁.S.r * X₁.S.N) := fun mu => if mu = 0 then 0 else wt mu
  have hwt' : ∀ a mu, 𝔪.YY a mu → wt' mu = (sg : ℤ) • eStd X₁.S.g _ τ a := by
    intro a mu h
    by_cases h0 : mu = 0
    · subst h0
      have ha : a ∈ X₁.S.HH X₁.M z₁ := (GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hx₀ V ev Y m t δ 𝔪 a).2 h
      have h1 : eStd X₁.S.g _ τ a = 0 := hτ a ha
      simp only [wt', if_pos rfl, h1, smul_zero]
    · simp only [wt', if_neg h0]
      exact hwt a mu h
  have hh : X₁.M.stalkHom z₁ (s * u * r) = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) * X₁.S.th (lab c + τ) / X₁.S.th x₀ := by
    rw [map_mul, map_mul, hs, hu, hr]
    field_simp [hcd.1, hx₀.1]
  obtain ⟨N, -, -, -, hN⟩ := hTw zt (s * u * r) hzt hh wt' hwt'
  obtain ⟨S, hS⟩ := hN 1
  have h1 := hS (insert 0 S) (Finset.subset_insert _ _)
  have hle : maximalIdeal V ^ 1 • N ≤ (maximalIdeal V : Submodule V V) :=
    Submodule.smul_le.2 fun a ha b _ => by
      rw [smul_eq_mul]; exact Ideal.mul_mem_right b _ (by simpa using ha)
  have h2 := hle h1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self 0 S)] at h2
  have h3 : ∑ mu ∈ (insert 0 S).erase 0, ev zt ^ (wt' mu).val * T mu c ∈ maximalIdeal V :=
    Ideal.sum_mem _ fun mu hmu => Ideal.mul_mem_left _ _
      (GlobalTheory.T.thetaModelMember_term_mem_maximalIdeal g n F W Z i X₁ z₁ act x₀ hx₀ V ev Y m t δ 𝔪 C lab hlab T hT c mu (Finset.ne_of_mem_erase hmu))
  have h0 : ev zt ^ (wt' 0).val * T 0 c = T 0 c := by simp [wt']
  rw [h0] at h2
  have h4 : ev (s * u * r) - T 0 c ∈ maximalIdeal V := by
    have := Ideal.add_mem _ h2 h3
    simpa [sub_add_eq_sub_sub, sub_add_cancel] using this
  have h5 := GlobalTheory.T.divisor_stalk_evaluation_linear_map_family g n F W Z i X₁ z₁ act x₀ hx₀ V ev Y m t δ 𝔪 C lab hlab T hT c r hr
  have h6 : (ev (s * u) - 1) * ev r ∈ maximalIdeal V := by
    have := Ideal.sub_mem _ h4 h5
    rw [map_mul] at this
    convert this using 1; ring
  exact (Ideal.mul_unit_mem_iff_mem _ (hrU.map ev)).1 h6

end GlobalTheory.Poinc.Sep.TwistResid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationIsModelOfChartsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_compactification_isModel_of_charts : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∃ (Y : Model Xo c (RingHom.id c.F)) (ε : Y.X ≅ S), Y.j ≫ ε.hom = j ∧ Y.s = ε.hom ≫ π ≫ zs ∧ ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t Y.t (ξ ≫ ε.inv)) := by
  first | exact @GlobalTheory.UChart.exists_model_of_charts | exact GlobalTheory.UChart.exists_model_of_charts | (intros; apply GlobalTheory.UChart.exists_model_of_charts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralCompactificationsExistStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_integral_compactifications_exist : UMinSt := by
  first | exact @GlobalTheory.UPoinc.uMinSt_holds | exact GlobalTheory.UPoinc.uMinSt_holds | (intros; apply GlobalTheory.UPoinc.uMinSt_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLabellingGaloisTransportDeeperLevel
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem uGalTransport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → UIsLab D.X (D.lift ct (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D σ s hs
  obtain ⟨a, hG, hfix⟩ := GlobalTheory.T.exists_semilinear_label_action_of_galois_deeper E H Dw hpq l Xo cf C X₁ D σ
  exact ⟨a, hfix, fun p _ z₁ ct y h h' yy hL =>
    GlobalTheory.T.unitary_labelling_transport_galois_conjugate E H Dw hpq l Xo cf C X₁ D σ s hs a hG hfix p z₁ ct y h h' yy hL⟩

end GlobalTheory.UPoinc
end
end

