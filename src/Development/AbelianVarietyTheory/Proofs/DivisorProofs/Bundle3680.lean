import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3677
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3678
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesPrincipalAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelFieldClass

theorem dense_generic {A V : Type} [CommRing A] [CommRing V] [IsDomain V] (β : A →+* V)
    (hβ : Function.Injective β) : Dense {x : Sp V | (spMap β x).asIdeal = ⊥} := by
  let ξ : Sp V := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)
  have hξ : ξ ∈ {x : Sp V | (spMap β x).asIdeal = ⊥} := by
    show (PrimeSpectrum.comap (CommRingCat.ofHom β).hom ⟨⊥, Ideal.isPrime_bot⟩).asIdeal = ⊥
    simp only [PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom]
    exact (RingHom.injective_iff_ker_eq_bot β).1 hβ
  have hd : Dense ({ξ} : Set (Sp V)) := by
    rw [dense_iff_closure_eq]
    show closure ({(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)} : Set (PrimeSpectrum V)) = Set.univ
    rw [PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_bot
  exact hd.mono (Set.singleton_subset_iff.2 hξ)

theorem classifies_algClosed : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp K ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ _ β c hc
  obtain ⟨V, _, _, βV, π, cV, hinj, hcomp, hpr, hpb⟩ := GlobalTheory.T.principal_siegel_object_exists_charZero_lift g n hg hn hodd K β c hc
  obtain ⟨f, hf, hfpb⟩ := F.rep (Sp V) (spMap βV) cV inferInstance (dense_generic βV hinj) hpr
  refine ⟨spMap π ≫ f, ?_, GlobalTheory.SiegelPullComp.pb_comp hfpb hpb⟩
  rw [Category.assoc, hf, ← hcomp]
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.SiegelFieldClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioInEmbeddingRange
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2 Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigTop.Fun

theorem sqRatio_mem_of {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T)
    (W : G.Weil) (S : GridChoice W Set.univ) (ρ : RealMatch W) (c : Fin D.R.m → Fin D.R.m → T → ℂ)
    (hstd : IsStdChar D W.ψ (-1)) (hN : NumbersIn D.what₂.embLL S μ₀)
    (hC : ∀ i j t, SquareNonzero W S.B ρ t i j ∧ c i j t ≠ 0) (hK : ∀ i j t, IsSquareConst W S.B ρ t i j (c i j t))
    (hLN : ∀ i j : Fin D.R.m, (∀ t, ∃ Λ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ ∧
      ∀ s : ℤ, 1 - (GlobalTheory.SqTop.e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → Λ s ≠ 0))
    (hTX : ∀ i j : Fin D.R.m, ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X ∧ X.IsConst W.ψ W.θ c0)
    (hTW : ∀ (i j : Fin D.R.m) (t : T) (c c₀ : ℂ) (A A' WW : HSp D) (X : Tri T A A' WW)
      (c0 : T → ℂ) (Λ Λ₀ : ℂ → ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c → SquareNonzero W S.B ρ μ₀ i j →
      IsSquareConst W S.B ρ μ₀ i j c₀ → IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 → GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
      GlobalTheory.CMVal.IsHeckeL (nuH G μ₀ i j) Λ₀ → ∃ u : Fin (pp D j + qq D j) → ℂ,
        (∀ k, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (u k) 1) ∧
        ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧
          c / c₀ * ∏ k ∈ range (qq D j), Λ (eTop D i j + k + 1 : ℕ) / Λ₀ (eTop D i j + k + 1 : ℕ) =
            D.what₂.embLL ζ * (∏ k, u k) * (c0 t / c0 μ₀) *
              ∏ k ∈ range (pp D j), Λ (eTop D i j + qq D j - k : ℕ) / Λ₀ (eTop D i j + qq D j - k : ℕ))
    (hBF : ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
      ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam)
    (i j : Fin D.R.m) (t : T) : c i j t / c i j μ₀ ∈ Set.range D.what₂.embLL := by
  have hF : ∀ z : ℂ, z ∈ Set.range D.what₂.embLL ↔ z ∈ D.what₂.embLL.fieldRange := fun z => Iff.rfl

  obtain ⟨A₀, A₀', WW₀, X₀, -, hX₀, -⟩ := hTX i j
  obtain ⟨A, A', WW, X, hX, hS⟩ := hN.bottom i j ⟨A₀, A₀', WW₀, X₀, hX₀⟩
  obtain ⟨lam, hlam⟩ := hBF i j A A' WW X hX
  have hI := hX.is
  have hi' : ∀ t P g, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P g) X.fd' X.m' := fun t P g =>
    (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D W.ψ false A' WW _ _ (X.ω' t) X.m' X.fd' _ (hI.weil' t) (GlobalTheory.ConstRatio.posDef_of_std hX.std')
      hI.meas'.1 hI.meas'.2 (GlobalTheory.Chain.InnerSteps.theta_pureTensorO hI.isVac.1 hI.isVac.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f hI t).2 P)).1 g
  have hr := hS.rationalSums (fun t P g => hlam.2.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1 t P g) hi'
  have hrat := GlobalTheory.ConstRatio.ratIn_of_definite hI (GlobalTheory.ConstRatio.posDef_of_std hX.std) (GlobalTheory.ConstRatio.posDef_of_std hX.std')
    (GlobalTheory.ConstRatio.posDef_of_std hX.stdW) hlam hr μ₀
  haveI : Nonempty T := ⟨μ₀⟩
  have hcst : X.IsConst W.ψ W.θ lam := hlam.isConst

  obtain ⟨Λ, hΛ, hΛne⟩ := hLN i j t
  obtain ⟨Λ₀, hΛ₀, hΛ₀ne⟩ := hLN i j μ₀
  obtain ⟨u, hu, ζ, -, heq⟩ := hTW i j t (c i j t) (c i j μ₀) A A' WW X lam Λ Λ₀ (hC i j t).1 (hK i j t) (hC i j μ₀).1
    (hK i j μ₀) hX hcst hΛ hΛ₀
  rw [hF]
  obtain ⟨hn1, -, -, hn4, -, -, -, hn8, hn9⟩ := Model.tower_numbers (D := D) i j
  have hne : ∀ L : ℂ → ℂ, (∀ s : ℤ, 1 - (e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → L s ≠ 0) →
      ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j → L (n : ℂ) ≠ 0 := fun L h n h1 h2 => by
    have := h n (by omega) (by exact_mod_cast h2)
    simpa using this
  have hs : ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j →
      Λ (n : ℂ) / Λ₀ (n : ℂ) ∈ D.what₂.embLL.fieldRange ∧ Λ (n : ℂ) / Λ₀ (n : ℂ) ≠ 0 := fun n h1 h2 =>
    ⟨(hF _).1 (hN.ratios i j t Λ Λ₀ hΛ hΛ₀ n h1 (by omega) (hne Λ₀ hΛ₀ne n h1 h2)),
      div_ne_zero (hne Λ hΛne n h1 h2) (hne Λ₀ hΛ₀ne n h1 h2)⟩
  have hP1 : ∀ k ∈ range (qq D j), Λ ((eTop D i j + k + 1 : ℕ) : ℂ) / Λ₀ ((eTop D i j + k + 1 : ℕ) : ℂ) ∈
      D.what₂.embLL.fieldRange ∧ Λ ((eTop D i j + k + 1 : ℕ) : ℂ) / Λ₀ ((eTop D i j + k + 1 : ℕ) : ℂ) ≠ 0 := fun k hk =>
    hs _ (by omega) (by have := mem_range.1 hk; omega)
  have hP2 : ∀ k ∈ range (pp D j), Λ ((eTop D i j + qq D j - k : ℕ) : ℂ) / Λ₀ ((eTop D i j + qq D j - k : ℕ) : ℂ) ∈
      D.what₂.embLL.fieldRange := fun k hk =>
    (hs _ (by have := mem_range.1 hk; omega) (by omega)).1
  have hU : (∏ k, u k) ∈ D.what₂.embLL.fieldRange := prod_mem fun k _ => by
    obtain ⟨b, g, g', -, -, h⟩ := hu k
    rw [h, mul_one]
    exact RingHom.mem_fieldRange.2 ⟨_, rfl⟩
  have hl : lam t / lam μ₀ ∈ D.what₂.embLL.fieldRange := by
    obtain ⟨-, y, hy⟩ := hrat t
    exact RingHom.mem_fieldRange.2 ⟨_, hy⟩
  rw [eq_div_of_mul_eq (prod_ne_zero_iff.2 fun k hk => (hP1 k hk).2) heq]
  exact div_mem (mul_mem (mul_mem (mul_mem (RingHom.mem_fieldRange.2 ⟨ζ, rfl⟩) hU) hl) (prod_mem hP2))
    (prod_mem fun k hk => (hP1 k hk).1)

set_option maxHeartbeats 1600000 in

theorem sqRatio_atPt : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.RowClaim.ConstK → LNe → TriEx → Tower → (AtPt fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ i j t, GlobalTheory.RowTest.sqRatio ch i j t ∈ Set.range D.what₂.embLL) := by
  intro hP hAg hMa hSet hdl hC hLN hTX hTW
  have hBF := GlobalTheory.T.bottom_triangle_constant_ratio hP hAg hMa hLN
  obtain ⟨c3, h3⟩ := hSet.atPt hC
  obtain ⟨c5, h5⟩ := Model.gBig_and (Model.gBig_and hLN hTX) (Model.gBig_and hTW hBF)
  refine ⟨max c3 c5, fun CF hCF => ?_⟩
  have k3 : c3 ≤ CF := le_trans (by simp) hCF
  have k5 : c5 ≤ CF := le_trans (by simp) hCF
  obtain ⟨e0, he0, H⟩ := (h3 CF k3).and (hdl.and hSet)
  refine ⟨e0, he0, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  obtain ⟨C0, x₀, hg⟩ := h5 eps CF k5
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨y3, g3⟩, ⟨y5, g5⟩, ⟨y6, g6⟩⟩ := hK Fm CH hc hL
  refine ⟨max (max y3 y5) (max y6 x₀), fun x hx hle i p hp G W n a ha => ?_⟩
  have l3 : y3 ≤ x := le_trans (by simp) hle
  have l5 : y5 ≤ x := le_trans (by simp) hle
  have l6 : y6 ≤ x := le_trans (by simp) hle
  have l7 : x₀ ≤ x := le_trans (by simp) hle
  have hset := g6 x hx l6 i p hp ha.eser
  have hrec : Rec (Fm.L x i) := ⟨hset.size, hset.host, hset.hF, g5 x hx l5 i p hp⟩
  obtain ⟨⟨hLN', hTX'⟩, hTW', hBF'⟩ := hg C0 le_rfl _ (Fm.L x i) (Fm.L_eps x i)
    (by rw [Fm.L_x x i hx]; exact l7) hrec _ _ _ hset.core.lev G
  have hc := g3 x hx l3 i p hp G W n a ha
  have hstd : IsStdChar (Fm.D x i) W.ψ (-1) := (ha.is.weil.ψ : a.ch.W.ψ = _) ▸ hset.std
  exact fun i' j' t => sqRatio_mem_of G _ W a.S.toGridChoice a.rm a.c hstd ha.field hc ha.is.const
    (fun i j => (hLN' i j).1) (hTX' W hstd) (hTW' W a.S.toGridChoice a.rm hstd ha.field) (hBF' W hstd) i' j' t

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleIntegralVanishingStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stage_triangle_integral_vanishing : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∀ t t' P, X.I W.ψ W.θ t P = 0 → X.I W.ψ W.θ t' P = 0 := by
  first | exact @GlobalTheory.StageKer.kern_stage | exact GlobalTheory.StageKer.kern_stage | (intros; apply GlobalTheory.StageKer.kern_stage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifPullbackOfCanonicalOn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TChart.Taut

theorem unif_pull_of_canonOn : ∀ {g n : ℕ} {φ : InvFun ℤ} (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  intro g n φ C G₁ _ _ P hM hC V' _ _ _ θ hV hθ hs D' e hD
  obtain ⟨Q', e', hr, hd⟩ := hD
  have h₁ := GlobalTheory.T.tautological_base_data_pullback_along_map C.T C.R V' θ C.iw C.s C.form n C.Q C.e Q' _ hs C.data hd
  have h₂ := GlobalTheory.Mum.pullData_refines C.R V' θ C.Q Q' _ D'.toPre D'.tau_bimult e' h₁ hr
  refine GlobalTheory.T.canonical_mumford_family_pullback_local_uniformised C.R V' θ hM.1 hV hθ C.Q _ G₁ P hM.2.2.1 hC ?_ D' _ h₂
  rw [genericPoint_eq_bot_of_affine]
  show (∏ k, C.t k) ∉ Ideal.comap θ (⊥ : PrimeSpectrum V').asIdeal
  rw [Ideal.mem_comap, map_prod]
  exact Finset.prod_ne_zero_iff.2 fun k _ => hs (.inl k)

end GlobalTheory.TChart.Taut
end

