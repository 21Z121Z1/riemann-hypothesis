import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductRouteBEqExternalProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3181
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3184
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDataDescendsFiniteTypeSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFg

theorem spMap_subtype_inclusion' {R : Type} [CommRing R] {S₀ R₁ : Subring R} (h : S₀ ≤ R₁) :
    spMap R₁.subtype ≫ spMap (Subring.inclusion h) = spMap S₀.subtype := by
  rw [← Spec.map_comp]
  rfl

theorem smooth_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) (g : ℕ) (hB : SmoothOfRelativeDimension g B.hom) :
    SmoothOfRelativeDimension g ((Over.pullback f).obj B).hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback B.hom f) hB

theorem range_le {n : ℕ} {R : Type} [CommRing R] (β : cycAway n →+* R) (S₀ : Subring R)
    (h₁ : β (zetaAway n) ∈ S₀) (h₂ : ∀ hm : ((n : ℂ))⁻¹ ∈ cycAway n, β ⟨((n : ℂ))⁻¹, hm⟩ ∈ S₀) (x : cycAway n) :
    β x ∈ S₀ := by
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact h₁
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h₂ _
  | zero => exact (congrArg (· ∈ S₀) (map_zero β)).mpr S₀.zero_mem
  | one => exact (congrArg (· ∈ S₀) (map_one β)).mpr S₀.one_mem
  | add y z hy hz ihy ihz =>
    have e : β ⟨y + z, Subring.add_mem _ hy hz⟩ = β ⟨y, hy⟩ + β ⟨z, hz⟩ := by rw [← map_add]; rfl
    rw [e]; exact S₀.add_mem ihy ihz
  | neg y hy ihy =>
    have e : β ⟨-y, Subring.neg_mem _ hy⟩ = -β ⟨y, hy⟩ := by rw [← map_neg]; rfl
    rw [e]; exact S₀.neg_mem ihy
  | mul y z hy hz ihy ihz =>
    have e : β ⟨y * z, Subring.mul_mem _ hy hz⟩ = β ⟨y, hy⟩ * β ⟨z, hz⟩ := by rw [← map_mul]; rfl
    rw [e]; exact S₀.mul_mem ihy ihz

end GlobalTheory.SiegFg

namespace GlobalTheory.SiegFg

theorem siegPre_data_descends_fg : ∀ (g n : ℕ), 3 ≤ n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), ∃ (R₁ : Subring R) (β₁ : cycAway n →+* R₁) (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), Algebra.FiniteType ℤ R₁ ∧ R₁.subtype.comp β₁ = β ∧ IsAbelianScheme A₁ ∧ SmoothOfRelativeDimension g A₁.hom ∧ P₁.IsLB ∧ IsPullbackTriple c.A c.P (lvOf c) A₁ P₁ lv₁ (spMap R₁.subtype) := by
  intro g n hn R _ β c
  classical
  have h0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨h0⟩
  have hdim : SmoothOfRelativeDimension g c.A.hom :=
    relDim (ζ := (cycBase h0).ζ) (by omega) (isUnit_natCast h0) c
  have hm : ((n : ℂ))⁻¹ ∈ cycAway n := Subring.subset_closure (by simp)
  obtain ⟨S₀, B, _, φ, hF, hS₀, hB, hBd, hφ⟩ := GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring R g c.A
    {β (zetaAway n), β ⟨((n : ℂ))⁻¹, hm⟩} c.ab hdim
  have hβ : ∀ x, β x ∈ S₀ := range_le β S₀ (hF (by simp)) (fun _ => hF (by simp))
  have : IsCommMonObj B := hB.comm
  have : IsProper B.hom := hB.proper
  have : Smooth B.hom := hB.smooth
  have : QuasiCompact (B ⊗ B).hom := by
    change QuasiCompact (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
  have : QuasiSeparated (B ⊗ B).hom := by
    change QuasiSeparated (pullback.fst B.hom B.hom ≫ B.hom); infer_instance

  obtain ⟨φ₂, hsq⟩ := GlobalTheory.SiegDesc.exists_isSquare hφ.1.w
  obtain ⟨SP, hSP⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring R S₀ (c.A ⊗ c.A).left (B ⊗ B).left (c.A ⊗ c.A).hom
    (B ⊗ B).hom φ₂ c.P (GlobalTheory.SiegDesc.isPullback_of_isSquare hφ.1 hsq) c.isLB

  have hw : ∀ a : Std g n, ((lvOf c a).left ≫ φ) ≫ B.hom = spMap S₀.subtype ≫ 𝟙 _ := fun a => by
    have e : (lvOf c a).left ≫ c.A.hom = 𝟙 _ := Over.w (lvOf c a)
    rw [Category.assoc, hφ.1.w, reassoc_of% e, Category.comp_id]
  choose SL hSL using fun a : Std g n => GlobalTheory.morphism_descends_to_subring R S₀ (Sp R) (Sp S₀) B.left (𝟙 _) (𝟙 _)
    B.hom (spMap S₀.subtype) ((lvOf c a).left ≫ φ) IsPullback.of_id_snd (hw a)

  let T : Finset R := SP ∪ Finset.univ.biUnion SL
  let R₁ : Subring R := (Algebra.adjoin S₀ (T : Set R)).toSubring
  have hFT : Algebra.FiniteType ℤ R₁ :=
    GlobalTheory.SpreadGroup.finiteType_of_fg hS₀ (Subalgebra.fg_adjoin_finset T)
  have h : S₀ ≤ R₁ := fun x hx => Subalgebra.algebraMap_mem (Algebra.adjoin S₀ (T : Set R)) (⟨x, hx⟩ : S₀)
  have hT : (T : Set R) ⊆ R₁ := Algebra.subset_adjoin
  have hSPs : (SP : Set R) ⊆ R₁ := fun x hx => hT (by simp [T, Finset.mem_coe.1 hx])
  have hSLs : ∀ a, (SL a : Set R) ⊆ R₁ := fun a x hx => hT (by
    simp only [T, Finset.coe_union, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true]
    exact Or.inr (Set.mem_iUnion.2 ⟨a, hx⟩))
  have hj : spMap R₁.subtype ≫ spMap (Subring.inclusion h) = spMap S₀.subtype := spMap_subtype_inclusion' h

  let A₁ : Over (Sp R₁) := (Over.pullback (spMap (Subring.inclusion h))).obj B
  have hA₁ : IsAbelianScheme A₁ :=
    { comm := by infer_instance
      smooth := by show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := hB.geomConnected
        show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hA₁d : SmoothOfRelativeDimension g A₁.hom := smooth_pull _ B g hBd
  have hpb := Pdiv.PullbackComparison.isGrpPullback (spMap (Subring.inclusion h)) B
  let ψ : c.A.left ⟶ A₁.left := pullback.lift φ (c.A.hom ≫ spMap R₁.subtype)
    (by rw [hφ.1.w, Category.assoc, hj])
  have hψ₁ : ψ ≫ Pdiv.PullbackComparison.pφ (spMap (Subring.inclusion h)) B = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = c.A.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hgp : IsGrpPullback c.A A₁ (spMap R₁.subtype) ψ :=
    IsGrpPullback.cancel hpb (by rw [hψ₁, hj]; exact hφ) hψ₂

  obtain ⟨ψ₂, hsqψ⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ₂
  obtain ⟨P₁, hP₁, hiso⟩ := hSP R₁ h hSPs (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom
    (Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) B) ψ₂
    (GlobalTheory.SiegDesc.isPullback_of_isSquare hpb.1 (Pdiv.PullbackComparison.isSquare _ B))
    (GlobalTheory.SiegDesc.isSquare_comp hψ₁ hsqψ (Pdiv.PullbackComparison.isSquare _ B) hsq) (GlobalTheory.SiegDesc.isSquare_w hψ₂ hsqψ)

  choose ψa hψa using fun a : Std g n => hSL a R₁ h (hSLs a) (Sp R₁) (𝟙 _) (spMap (Subring.inclusion h))
    (spMap R₁.subtype) IsPullback.of_id_snd hj (by simp)
  let l : Std g n → (Sp R₁ ⟶ A₁.left) := fun a => pullback.lift (ψa a) (𝟙 _)
    (by rw [(hψa a).2, Category.comp_id, Category.id_comp])
  have hl₁ : ∀ a, l a ≫ pullback.fst _ _ = ψa a := fun a => pullback.lift_fst _ _ _
  have hl₂ : ∀ a, l a ≫ A₁.hom = 𝟙 _ := fun a => pullback.lift_snd _ _ _
  let lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁) := fun a => Over.homMk (l a) (hl₂ a)
  refine ⟨R₁, β.codRestrict R₁ (fun x => h (hβ x)), A₁, inferInstance, P₁, lv₁, hFT, by ext; rfl, hA₁, hA₁d, hP₁,
    ψ, ψ₂, hgp, hsqψ.1, hsqψ.2, hiso, fun a => ?_⟩
  have e : (lvOf c a).left ≫ c.A.hom = 𝟙 _ := Over.w (lvOf c a)
  apply pullback.hom_ext
  · change (lvOf c a).left ≫ ψ ≫ pullback.fst _ _ = spMap R₁.subtype ≫ l a ≫ pullback.fst _ _
    rw [hl₁]
    exact (congrArg ((lvOf c a).left ≫ ·) hψ₁).trans (hψa a).1.symm
  · change (lvOf c a).left ≫ ψ ≫ A₁.hom = spMap R₁.subtype ≫ l a ≫ A₁.hom
    rw [hψ₂, hl₂, reassoc_of% e, Category.comp_id]

end GlobalTheory.SiegFg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelEqUnitNormMulTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallKernel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumB skewGram blkU conjU xiV xiV₁ boxB alpha beta)
open GlobalTheory.RouteSeesaw
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem end_finsupp_sum_apply {α β : Type} (A : Module.End ℂ (β → ℂ)) (Θ : α →₀ ℂ) (f : α → β → ℂ) (w : β) :
    A (fun x => Θ.sum fun d c => c * f d x) w = Θ.sum fun d c => c * A (f d) w := by
  have e : (fun x => Θ.sum fun d c => c * f d x) = ∑ d ∈ Θ.support, Θ d • f d := by
    funext x
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  simp only [Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (m + n) := by
  intro a
  have e1 := h a
  have e2 := h' a
  simp only [MonoidHom.div_apply, Circle.coe_div] at *
  rw [e1, e2]
  split_ifs
  · simp
  · have hm : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [div_eq_iff (by simp), add_comm, pow_add, mul_assoc, hm, mul_one]

theorem data_theta_small {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)}
    (hΘ : IsMatched B t ρ i j Θ Θ') : ∀ d ∈ Θ'.support,
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hΘ
  intro d hd
  have hsupp := Finsupp.support_sum hd
  simp only [Finset.mem_biUnion] at hsupp
  obtain ⟨P, -, hP⟩ := hsupp
  have hsupp2 := Finsupp.support_sum hP
  simp only [Finset.mem_biUnion] at hsupp2
  obtain ⟨d', hd', hd'2⟩ := hsupp2
  have hdd := Finset.mem_singleton.1 (Finsupp.support_single_subset hd'2)
  subst hdd
  obtain ⟨h1, h2⟩ := hloc d' hd'
  have v1 := (ρ.vT_is t (i : ℕ) (j : ℕ) i.2.le j.2).2.theta
  have v2 := (ρ.vX_is (i : ℕ) (j : ℕ) i.2 j.2.le).2.theta
  have t1 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h1.2 v1
  have t2 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h2.2 v2
  exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩

set_option maxHeartbeats 1000000 in

theorem seesaw_swapped {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin (spW₁ G i j).rank)
    (e₂ : Fin S'.rank ≃ Fin (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank)
    (hT' : T'.gramᵀ = -((spW₁ G i j).gram.submatrix e₁ e₁))
    (hS' : S'.gram⁻¹ = -((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ.submatrix e₂ e₂))
    (ω : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ))
    (hω : IsWeilDatumO W.ψ S' T' (alpha G t i j / beta G i j) (alpha G t i j) ω)
    (f₁ : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ) (f₂ : WO (G.pS (.chi i j)) (G.pT (.chi i j)) → ℂ)
    (hf₁ : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) f₁)
    (hf₂ : IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) f₂)
    (g : GA D (spV G i j)) (u : GA D (spW₁ G i j)) (g₁ : GA D (spV₁ G i j)) (g' : GA D S') (h' : GA D T')
    (hh : Formalism.L2.Theta.mt T' h' = ((Formalism.L2.Theta.mt _ u).map (cA D)).submatrix e₁ e₁)
    (hg : Formalism.L2.Theta.mt S' g' = ((Formalism.L2.Theta.mt _ (GlobalTheory.SquareComm.blk _ _ (g, g₁))⁻¹).submatrix e₂ e₂)ᵀ) :
    W.kerA (.down t i j) f₁ g u * W.kerA (.right i j) f₂ u g₁ =
      xiV G i j g * xiV₁ G t i j g₁ * ω (g', h') (fun x => box2 f₁ (GlobalTheory.SeesawSmall.adjFn (spW₁ G i j) (spV₁ G i j) f₂)
        (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) ((spW₁ G i j).gram.map (incA D)) :
          Matrix (Fin (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank) (Fin (spW₁ G i j).rank) (AE D))) 0 := by
  have r₁ : T'.rank = (spW₁ G i j).rank := by simpa using Fintype.card_congr e₁
  have r₂ : S'.rank = (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank := by simpa using Fintype.card_congr e₂
  obtain ⟨ωA, hA⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D W.ψ W.ψ_std (spW₁ G i j)
    (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) (alpha G t i j) (alpha G t i j / beta G i j)
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecT hω.hecS (r₁ ▸ hω.resT) (r₂ ▸ hω.resS)
  obtain ⟨hbox, hker⟩ := GlobalTheory.SeesawSmall.seesaw_small hL W t i.2 j.2 ωA hA f₁ f₂ hf₁ hf₂
  rw [hker g u g₁, GlobalTheory.BigSeesaw.swap_eq _ _ S' T' e₁ e₂ hT' hS' hA hω hbox u _ g' h' hh hg]
  rfl

set_option maxHeartbeats 1000000 in

theorem kerSmall_eq_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∀ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB →
    ∃ ξ : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) j)) → ℂ, (∀ x, ‖ξ x‖ = 1) ∧
      ∀ g u, kerSmall W Θ' g g₁ u =
        ξ (g, g₁) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' ΦB (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁)) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv Φ hΦ
  refine ⟨fun x => xiV G i j x.1 * xiV₁ G t i j x.2, fun x => ?_, fun g u => ?_⟩
  · simp only [xiV, xiV₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.flatDet, norm_mul, Circle.norm_coe, mul_one]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.WeilSchrodingerHerm.main D Bs hTr.base _ Γ.V' _ _ hTr.geo.hV'
  obtain ⟨hJ, LS, hLS, h4, h5, h6⟩ := GlobalTheory.WeilSchrodingerSkew.main D Bs hTr.base _ Γ.W _ _ hTr.geo.hW
  have hξ0 : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have eA : Γ.V'.J = (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat h3 (fun _ => (0, 0))).gramᵀ := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; exact (Matrix.transpose_transpose _).symm
  have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
      inv_mul_cancel₀ (neg_ne_zero.2 hξ0), one_smul])
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 •
      (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0))).gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ0, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext a b
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  obtain ⟨ω, hω, -, hth⟩ := GlobalTheory.WeilBridge.exists_theta_eq D Bs hTr.base
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat h3 (fun _ => (0, 0))) Γ.V' Γ.W _ _ _ _
    hTr.geo.hV' hTr.geo.hW eA eB
    Γ.M' hTr.geo.hM' X.α (X.α / X.β) hTr.chars.heckeα (isHecke_div hTr.chars.heckeα hTr.chars.heckeβ) hTr.chars.resα
    (resEtaPow_div hTr.chars.resα hTr.chars.resβ) om' hTr.weil'
  rw [h.ψ, h.α, h.β] at hω
  obtain ⟨g', h', hh', hg'⟩ := GlobalTheory.WeilSchrodinger.match_pair D
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat h3 (fun _ => (0, 0))) Γ.V'.J Γ.W.J (-1) eA eB
    (conjU (spW₁ G i j) (-1) h.JW₁ u) (blkU (spV G i j) (spV₁ G i j) e h.JWW (g, g₁))
  have key := hth _ _ g' h' hh' hg' Φ hΦ.1
  refine Eq.trans ?_ (congrArg (fun z => xiV G i j g * xiV₁ G t i j g₁ * z) key.symm)
  have htr : GlobalTheory.WeilSchrodinger.thetaTr D.host.F Γ.M'.co Bs.ψ Φ =
      fun w => Θ'.sum fun d c => c * boxB e d w := by
    funext w
    show GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho Bs.ψ w Φ) = _
    rw [h.ψ, hΦ.2 w]
    rfl
  refine Eq.trans ?_ (congrArg (fun f => xiV G i j g * xiV₁ G t i j g₁ * ω (g', h') f 0) htr.symm)
  refine Eq.trans ?_ (congrArg (fun z => xiV G i j g * xiV₁ G t i j g₁ * z)
    (end_finsupp_sum_apply (ω (g', h')) Θ' (boxB e) 0).symm)
  rw [kerSmall, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨t1, t2⟩ := data_theta_small W B ρ t i j hΘ d hd
  let e₂ : Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ Fin ((spV G i j).rank + (spV₁ G i j).rank) :=
    e.symm.trans finSumFinEquiv
  have hb : ∀ {R : Type} [CommRing R] (A : Matrix (Fin (spV G i j).rank) (Fin (spV G i j).rank) R)
      (B : Matrix (Fin (spV₁ G i j).rank) (Fin (spV₁ G i j).rank) R),
      (GlobalTheory.Doubling.blkMat finSumFinEquiv A B).submatrix e₂ e₂ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A B := fun A B => by
    ext a b
    simp [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, e₂]
  have hJ' : Γ.W.J = D.host.xi0 • ((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂ := by
    refine h.JWW.trans (congrArg (D.host.xi0 • ·) ?_)
    rw [GlobalTheory.Doubling.gram_hsum, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← hb]
    rfl
  have hT' : (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat h3 (fun _ => (0, 0))).gramᵀ =
      -((spW₁ G i j).gram.submatrix (Equiv.refl _) (Equiv.refl _)) := by
    rw [← eA]
    show Γ.V'.J = -(spW₁ G i j).gram
    rw [h.JW₁, neg_one_smul]
  have hS' : (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0))).gram⁻¹ =
      -(((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    refine e1.trans ?_
    rw [hJ', smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hξ0, neg_one_smul]
  have k := seesaw_swapped hL W t i j
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat h3 (fun _ => (0, 0)))
    (Equiv.refl (Fin (spW₁ G i j).rank)) e₂ hT' hS' ω hω d.1.2 d.2 t1 t2 g u g₁
    g' h' hh' (by
      rw [hg', ← map_inv, Prod.inv_mk, GlobalTheory.SquareComm.mt_blk]
      exact congrArg transpose (hb (Formalism.L2.Theta.mt _ g⁻¹) (Formalism.L2.Theta.mt _ g₁⁻¹)).symm)
  refine (congrArg (fun z => Θ' d * z) k).trans ?_
  rw [mul_left_comm]
  refine congrArg (fun f => xiV G i j g * xiV₁ G t i j g₁ * (Θ' d * ω (g', h') f 0)) ?_
  funext x
  exact (GlobalTheory.SeesawSmall.thetaSquareProductRouteB_eq_externalProduct e d x).symm

end GlobalTheory.SmallKernel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionCountStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairDet_norm_le_attained_and_sub_norm_lt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g g' : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (e' : Fin g' → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → IsTanBasis t x e' → ∀ (N : ℕ) (c : Fin N → TorsChar t x (p ^ 2)) (h : Fin N → Fin g → ↥(intO ℂ_[p])) (h' : Fin N → Fin g' → ↥(intO ℂ_[p])), (∀ c' : TorsChar t x (p ^ 2), ∃ j, Agree c' (c j)) → (∀ j, DlogIs t p 2 (c j) e (h j)) → (∀ j, DlogIs t p 2 (c j) e' (h' j)) → ∀ (m k : ℕ) (hk : k ≤ m) (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → Fin g → ℂ_[p]) (a' : Fin m → Fin g' → ℂ_[p]), LinearIndependent ℂ_[p] a → (∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) (a l) (u l)) → (∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e' i) (a' l) (u l)) → ∀ ν : ℝ, ν = ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ℂ_[p]).subtype ≫ x) (latHT t p (spMap (intO ℂ_[p]).subtype ≫ x)) u (Fin.castLE hk l) → (∀ l, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ℂ_[p]).subtype ≫ x) (latHT t p (spMap (intO ℂ_[p]).subtype ≫ x)) u l) ∧ (∀ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ ≤ ν) ∧ (∃ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ = ν) ∧ ∀ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ - pairDet (fun j i => (h' j i : ℂ_[p])) a' hk σ‖ < ν := by
  first | exact @GlobalTheory.HtGen.PointDet.pairDet_htLattice | exact GlobalTheory.HtGen.PointDet.pairDet_htLattice | (intros; apply GlobalTheory.HtGen.PointDet.pairDet_htLattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentValuePullbackCrystallineFormDualNumbers
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ParPt

theorem tanVal_pullForm_ofModule : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) (A' : Over (Sp R')) (φ : A'.left ⟶ A.left) (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (v : epsR R' ⟶ A') (hy : (v.left ≫ φ) ≫ A.hom ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R'))) (f : Form (A.hom ≫ 𝟙 (Sp R))), tanVal v (m.pullForm f) = TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val (v.left ≫ φ) hy f.1) := by
  intro R R' _ _ _ A A' φ m v hy f
  let E := SqExt.ofModule R R' R'
  let E' := SqExt.dual R'
  have hy' := pt_w v
  have hc : ∀ r : R, RingHom.id (DualNumber R') (algebraMap R (DualNumber R') r) =
      algebraMap R' (DualNumber R') (algebraMap R R' r) := fun r =>
    IsScalarTower.algebraMap_apply R R' (DualNumber R') r
  have e₀ : spMap (RingHom.id R') ≫ spMap (E.π : E.C →+* E.B) ≫ v.left ≫ φ =
      (spMap (E'.π : E'.C →+* E'.B) ≫ v.left) ≫ φ := by
    rw [Category.assoc, ← Category.assoc, ← Cris.spMap_comp]
    rfl
  have e : spMap (RingHom.id (DualNumber R')) ≫ v.left ≫ φ = v.left ≫ φ := by
    rw [Cris.spMap_id, Category.id_comp]
  let Φ : E.thick _ (E.red_w hy) ⟶ m.obj (E'.thick _ (E'.red_w hy')) :=
    { φ := { RingHom.id (DualNumber R') with commutes' := hc }
      φ₀ := RingHom.id R'
      comm := fun b => rfl
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun a ha => ha
      pt := e₀ }
  let a : Thick.triv E.C _ hy ⟶ m.obj (Thick.triv E'.C _ hy') :=
    Thick.trivHom { RingHom.id (DualNumber R') with commutes' := hc } e
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hy')) :=
    Thick.trivHom { RingHom.id R' with commutes' := fun _ => rfl } e₀
  have k1 := Form.ev_sq f a (m.functor.map (E'.idHom hy')) (E.idHom hy) Φ rfl rfl fun _ => rfl
  have k2 := Form.ev_sq f b (m.functor.map (E'.secHom (E'.red_w hy') E'.i E'.π_i))
    (E.secHom (E.red_w hy) E.i E.π_i) Φ rfl rfl fun c => rfl
  have k : E'.val v.left hy' (m.pullForm f).1 = E.val (v.left ≫ φ) hy f.1 :=
    (congrArg₂ (fun u v : E'.C => u - v) k2 k1).trans
      (add_sub_add_right_eq_sub (G := E'.C) _ _ _)
  rw [tanVal_apply]
  exact congrArg (TrivSqZeroExt.snd (R := R')) k

end GlobalTheory.ParPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeGeometricPointsOfGenericDvrStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateSimilitude_geometric_points_of_generic_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (gm : R →+* W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (P : LB (G2 G).left), P.IsLB → ∀ (y : D.La → (𝟙_ (Over (Sp W)) ⟶ G)), (∀ x x', y (x + x') = y x * y x') → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k), ∃ I : TateIsoO D k (Over.mk (spMap (β.comp (algebraMap W L))) ⟶ G) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)), ∀ x, toUnit _ ≫ y x = I.ev N x) → ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k), ∃ I : TateIsoO D k (Over.mk (spMap β) ⟶ G) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)), ∀ x, toUnit _ ≫ y x = I.ev N x := by
  first | exact @GlobalTheory.HTGeomExt.tateIsoO_geom_of_generic | exact GlobalTheory.HTGeomExt.tateIsoO_geom_of_generic | (intros; apply GlobalTheory.HTGeomExt.tateIsoO_geom_of_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalPointTransportFieldMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalPoint_transport_fieldMap : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D) ββ' w', Function.Injective f → D.TauBimult → From T ω s ε n D₀.toPre e β ββ w → From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' → ∀ (F₀ : Type) [Field F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ (a : Fin T.r → ℤ) (g₀ : GtPtF D₀.toPre F₀) (g : GtPtF D F), TautPt T ω s ε n D₀.toPre e β ββ w F₀ a g₀ → Tr f hD j g₀ g → TautPt T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' F a g := by
  first | exact @GlobalTheory.TautTransport.tautPt_tr | exact GlobalTheory.TautTransport.tautPt_tr | (intros; apply GlobalTheory.TautTransport.tautPt_tr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalPointZeroAndPeriodStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalPoint_zero_and_period : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (g : GtPtF D F), (TautPt T ω s ε n D e β ββ w F 0 g → g.IsZero) ∧ ∀ y : D.X, TautPt T ω s ε n D e β ββ w F ((n : ℤ) • e y) g → GtPtF.IsIota y g := by
  first | exact @GlobalTheory.TInj.tautPt_zero_iota | exact GlobalTheory.TInj.tautPt_zero_iota | (intros; apply GlobalTheory.TInj.tautPt_zero_iota <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegDataPeriodsBalancedMatrixAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TensBal

theorem transpose_mul_eq {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det)
    (a : TensO (symUnitOf W h)) :
    (TensO.mat _ a).transpose * (W + W.transpose) = (W + W.transpose) * TensO.mat _ (star a) := by
  have hb : ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose := rfl
  rw [TensO.star_def]
  show _ = (W + W.transpose) * (((((symUnitOf W h).1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (TensO.mat _ a).transpose * ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ)))
  rw [hb.symm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem tauBal_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), letI := T.mod (symUnitOf W h); ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) (fun y => a • y) (fun y => star a • y) := by
  intro R _ _ _ _ D D' r W h _ T a
  exact GlobalTheory.T.tensorDegeneration_tauBalanced_of_adjointIntMatrices R _ D D' W T (TensO.mat _ a) (TensO.mat _ (star a)) (transpose_mul_eq W h a)

end GlobalTheory.Mum.TensBal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisSectionTupleQuotientsStatement
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transcendenceBasis_sectionTupleQuotients : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K) (l : Fin (D + 1)) (A : Subring K), Algebra.trdeg ℤ K = D → x l ≠ 0 → Algebra.FiniteType ℤ A → (∀ w ∈ A, IsIntegral (ratR x l) w) → (∀ w : K, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ w = a / b) → (∀ j, x j ≠ 0) ∧ AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) ∧ FiniteDimensional (ratF x) K := by
  first | exact @GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR | exact GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR | (intros; apply GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR <;> assumption)
end

