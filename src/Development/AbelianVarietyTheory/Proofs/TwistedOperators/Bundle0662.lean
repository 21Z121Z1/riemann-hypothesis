import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0540
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1732
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0638
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0657
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselFlatMapEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0618
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0285
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0157
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeForMatchedFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallKerInv

open GlobalTheory.FinPl

variable {D : D7}

theorem placeIdem_smul_offP {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {w : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D w ε) (hw : ¬ P w) {u : WO S T}
    (hu : u ∈ latO S T LS LT P) : algebraMap (AF D.host.F) (AE D) ε • u = 0 := by
  obtain ⟨β, rfl, -, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hx
    have hβα : β * α = 0 := by
      refine RestrictedProduct.ext _ _ fun y => ?_
      change evalV D.host.F y (β * α) = evalV D.host.F y 0
      rw [map_mul, map_zero]
      by_cases hy : y = w
      · subst hy; rw [hP y hw, mul_zero]
      · rw [h0 y hy, zero_mul]
    have hp : pairA D.host.F 0 β * pairA D.host.F 0 α = 0 := Prod.ext (mul_zero _) hβα
    ext i j
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = (0 : AE D)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp, TensorProduct.zero_tmul]
  | zero => rw [smul_zero]
  | add x x' _ _ h h' => rw [smul_add, h, h', add_zero]
  | neg x _ h => rw [smul_neg, h, neg_zero]

theorem idemSum_mul_offP {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {e : AE D} {Pset : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (he : IsIdemSum e Pset) (hv : ∀ PP ∈ Pset, ¬ P (PP.under (𝓞 D.host.F))) {u : WO S T}
    (hu : u ∈ latO S T LS LT P) (a b) : e * u a b = 0 ∧ cA D e * u a b = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have key : ∀ PP ∈ Pset, es PP * u a b = 0 ∧ cA D (es PP) * u a b = 0 := by
    intro PP hPP
    obtain ⟨⟨a1, a2, w, ε, hε, a3⟩, -⟩ := hes PP hPP
    have hw : ¬ P w := fun h => hv PP hPP (by
      rw [GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP w ε (hes PP hPP) hε a3]; exact h)
    have h0 := congrFun (congrFun (placeIdem_smul_offP hε hw hu) a) b
    rw [Matrix.smul_apply, smul_eq_mul, ← a3, Matrix.zero_apply] at h0
    have c1 : cA D (es PP) * cA D (es PP) = cA D (es PP) := by rw [← map_mul, a1]
    have c2 : cA D (es PP) * es PP = 0 := by rw [mul_comm, a2]
    refine ⟨?_, ?_⟩
    · linear_combination es PP * h0 - u a b * a1 - u a b * a2
    · linear_combination cA D (es PP) * h0 - u a b * c1 - u a b * c2
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).1
  · rw [map_sum, Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).2

theorem latO_le_true {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO S T LS LT fun _ => True := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, -, rest⟩
  exact ⟨α, hα, fun v h => absurd trivial h, rest⟩

end GlobalTheory.SmallKerInv

namespace GlobalTheory.SmallKerInv

open GlobalTheory.FinPl

variable {D : D7}

theorem om_fock_fix (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (LS : Lat S) (LT : Lat T) (P : Pl D → Prop)
    (hP : ∀ v, P v → IsSelfDualC S LS ∧ IsSelfDualC T LT ∧ Tame D v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS v ∧
      GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT v)
    (e : AE D) (Pset : Finset (Formalism.L2.DIV.Pl D.host.E)) (he : IsIdemSum e Pset)
    (hoff : ∀ PP ∈ Pset, ¬ P (PP.under (𝓞 D.host.F)))
    (f₀ φ f : WO S T → ℂ) (h₀ : IsThetaFunO ψ S T f₀)
    (hlat : IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) fun _ => True) f₀)
    (hth : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (LS : Set _) (LT : Set _) fun _ => True) 1 f₀ φ f)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (Q : PolF D T.rank S.rank) (κ : GA D S) (κ' : GA D T) (hκ : InK S LS P κ) (hκ' : InK T LT P κ') :
    om (κ, κ') (pureTensorO ψ θ S T sS sT BS BT f Q) = pureTensorO ψ θ S T sS sT BS BT f Q := by
  have hf : IsThetaFunO ψ S T f := GlobalTheory.GalLift.Vec.theta_of_thetaAt hW.std hθ hth h₀
  have hz : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) P, ∀ a b, e * u a b = 0 ∧ cA D e * u a b = 0 :=
    fun u hu a b => idemSum_mul_offP he hoff hu a b
  have hle := latO_le_true (S := S) (T := T) (LS : Set _) (LT : Set _) P
  have hvac : Vac ψ S T LS LT P f := by
    refine ⟨hf, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off ψ S T e _ 1 f₀ φ f hth (2 • u)
        (hz _ (AddSubgroup.nsmul_mem _ hu 2)) (hlat.1 u (hle hu))
    · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off ψ S T e _ 1 f₀ φ f hth u (hz u hu) (hlat.2 e' he' u (hle hu) hh)
  have hfix : om (κ, κ') f = f := GlobalTheory.VacFixP.vac_fix_on D ψ S T χS χT om hW LS LT P hP f hvac κ κ' hκ hκ'
  have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite ψ θ S T χS χT om hθ hW sS sT BS BT f
    (fun R => GlobalTheory.GalLift.Vec.theta_pureTensorO hW.std hθ sS BS sT BT hf R)
    κ (GlobalTheory.FinPl.SetCut.grpAt_le_GfC S P hκ.1) κ' (GlobalTheory.FinPl.SetCut.grpAt_le_GfC T P hκ'.1) 1
    (by rw [hfix, one_smul]) Q
  rw [this, one_smul]

theorem inK_one (S : HSp D) (L : Lat S) (P : Pl D → Prop) : InK S L P 1 := by
  refine ⟨one_mem _, fun y _ => ?_⟩
  have h : mt S 1 = 1 := rfl
  rw [h, Matrix.one_mulVec]

end GlobalTheory.SmallKerInv

namespace GlobalTheory.SmallKerInv

open GlobalTheory.FinPl

theorem kerSmall_inv : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁,
  ∃ (L : GlobalTheory.FinPl.Lat (G.V (.grid i j))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    L.FG ∧ Submodule.span D.host.E (L : Set (Fin (G.V (.grid i j)).rank → D.host.E)) = ⊤ ∧
    ∀ κ, GlobalTheory.FinPl.InK (G.V (.grid i j)) L (fun v => v ∉ S) κ → ∀ u, kerSmall W Θ' g g₁ (u * κ) = kerSmall W Θ' g g₁ u := by
  intro _ _ _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩⟩
  intro G W hW B ρ hρ t i j Θ Θ' hΘ g g₁
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, he, ⟨φ₁, φ₂, h1, -⟩, -⟩, -, rfl⟩ := hΘ
  have hm := W.om_is (.mu t i j) ⟨i.2.le, j.2⟩
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have s1 := (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have s2 := (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  set good : Pl D → Prop := fun v => Tame D v ∧
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrS (.mu t i j)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrT (.mu t i j)) v ∧
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrS (.chi (i : ℕ) j)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrT (.chi (i : ℕ) j)) v
    with hgood
  have hev : ∀ᶠ v : Pl D in Filter.cofinite, good v := by
    filter_upwards [GlobalTheory.FinPl.eventually_extUnram_two_notMem D,
      GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hm.hecS.1, GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hm.hecT.1,
      GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hc.hecS.1, GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hc.hecT.1]
      with v h0 h1 h2 h3 h4
    exact ⟨⟨h0.1, Or.inl h0.2⟩, h1, h2, h3, h4⟩
  have hfin : {v | ¬ good v}.Finite := Filter.eventually_cofinite.1 hev
  classical
  refine ⟨G.Λ (.grid i j), hfin.toFinset ∪ (locPl G t).image (fun PP => PP.under (𝓞 D.host.F)),
    s0.1.fg, s0.1.span_eq_top, ?_⟩
  intro κ hκ u
  have hgd : ∀ v, v ∉ hfin.toFinset ∪ (locPl G t).image (fun PP => PP.under (𝓞 D.host.F)) → good v := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 h))
  have hoff : ∀ PP ∈ locPl G t,
      ¬ (PP.under (𝓞 D.host.F) ∉ hfin.toFinset ∪ (locPl G t).image (fun PP => PP.under (𝓞 D.host.F))) :=
    fun PP hPP h => h (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))
  unfold kerSmall
  refine Finsupp.sum_congr fun d hd => ?_
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd''⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  have hdd := Finsupp.support_single_subset hd''
  rw [Finset.mem_singleton] at hdd
  subst hdd
  obtain ⟨⟨hsb1, hth1⟩, ⟨hsb2, hth2⟩⟩ := h1 d' hd'
  have hv1 := ρ.vT_is t i j i.2.le j.2
  have hv2 := ρ.vX_is i j i.2 j.2.le
  congr 1
  congr 1
  · show thetaKO (W.om (.mu t i j)) (u * κ) g _ = thetaKO (W.om (.mu t i j)) u g _
    unfold thetaKO
    have e1 : ((u * κ, g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (u, g) * (κ, 1) := by simp
    rw [e1, map_mul, Module.End.mul_apply]
    refine congrArg (fun x => W.om (.mu t i j) (u, g) x 0) ?_
    exact om_fock_fix _ _ _ _ _ _ _ hm W.θ_is _ _ _
      (fun v hv => ⟨s0, s1, (hgd v hv).1, (hgd v hv).2.1, (hgd v hv).2.2.1⟩) e _ he hoff _ _ _
      hv1.2.theta hv1.2.lat hth1 _ _ _ _ _ κ 1 hκ (inK_one _ _ _)
  · show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (u * κ) _ = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u _
    unfold thetaKO
    have e2 : ((negGA _ g₁, u * κ) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) =
        (negGA _ g₁, u) * (1, κ) := by simp
    rw [e2, map_mul, Module.End.mul_apply]
    refine congrArg (fun x => W.om (.chi (i : ℕ) j) (negGA _ g₁, u) x 0) ?_
    exact om_fock_fix _ _ _ _ _ _ _ hc W.θ_is _ _ _
      (fun v hv => ⟨isSelfDualC_neg s2, s0, (hgd v hv).1, (hgd v hv).2.2.2.1, (hgd v hv).2.2.2.2⟩) e _ he hoff _ _ _
      hv2.2.theta hv2.2.lat hth2 _ _ _ _ _ 1 κ (inK_one _ _ _) hκ

end GlobalTheory.SmallKerInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesaw
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.OscLie

theorem exists_lie_deriv_pol : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')), ∀ f ∈ G.M.Pol B.ψ B.emb,
      δ f ∈ G.M.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ
  choose T hT' using fun t : ℝ => GlobalTheory.T.exists_archOperator_unitaryW_seesaw B G X om om' hT (γ (Multiplicative.ofAdd t)) (hγ.2 _)
  have hvac : ∀ f₀, G.M.IsGauss B.ψ B.emb f₀ → f₀ ∈ G.M.Pol B.ψ B.emb := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hstab : ∀ u, At (evI F) u → ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      ActsD (evI F) (G.M.heisLine B.ψ u) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb := fun u hu f hf f₁ h =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h
  let N : Submodule ℂ (SInf F (Fin a × Fin (a + a'))) :=
    { carrier := {f | f ∈ G.M.Pol B.ψ B.emb ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) => T p.1 f p.2) ∧
        ∃ f' ∈ G.M.Pol B.ψ B.emb, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0}
      zero_mem' := ⟨zero_mem _, by simpa using contDiff_const, 0, zero_mem _, fun x => by simpa using hasDerivAt_const _ _⟩
      add_mem' := by
        rintro f g ⟨hf, hf1, f', hf', hf2⟩ ⟨hg, hg1, g', hg', hg2⟩
        refine ⟨add_mem hf hg, by simpa using hf1.add hg1, f' + g', add_mem hf' hg', fun x => ?_⟩
        show HasDerivAt (fun t => T t (f + g) x) ((f' + g') x) 0
        simp only [map_add, SchwartzMap.add_apply]
        exact (hf2 x).add (hg2 x)
      smul_mem' := by
        rintro c f ⟨hf, hf1, f', hf', hf2⟩
        refine ⟨Submodule.smul_mem _ c hf, by simpa using hf1.const_smul c, c • f', Submodule.smul_mem _ c hf', fun x => ?_⟩
        simpa using (hf2 x).const_mul c }
  have hPN : G.M.Pol B.ψ B.emb ≤ N := by
    refine sInf_le ⟨fun f₀ h => ?_, fun u hu f hf f₁ h => ?_⟩
    · exact ⟨hvac f₀ h, GlobalTheory.T.weilAction_oneParamSubgroup_gaussVacuum_smooth B G X om om' hT γ hγ T hT' f₀ h⟩
    · obtain ⟨hf0, hf1, hf2⟩ := hf
      exact ⟨hstab u hu f hf0 f₁ h, GlobalTheory.T.smooth_weilOrbit_preserved_by_heisenbergDerivatives B G X om om' hT γ hγ T hT' u hu f hf0 hf1 hf2 f₁ h⟩
  have hex : ∀ f : G.M.Pol B.ψ B.emb, ∃ f' : SInf F (Fin a × Fin (a + a')), f' ∈ G.M.Pol B.ψ B.emb ∧
      ∀ x, HasDerivAt (fun t => T t (f : SInf F (Fin a × Fin (a + a'))) x) (f' x) 0 := fun f => by
    obtain ⟨-, -, f', hf', h⟩ := hPN f.2
    exact ⟨f', hf', h⟩
  choose d hdP hd using hex
  have huniq : ∀ (f g₁ g₂ : SInf F (Fin a × Fin (a + a'))), (∀ x, HasDerivAt (fun t => T t f x) (g₁ x) 0) →
      (∀ x, HasDerivAt (fun t => T t f x) (g₂ x) 0) → g₁ = g₂ := fun f g₁ g₂ h₁ h₂ =>
    SchwartzMap.ext fun x => (h₁ x).unique (h₂ x)
  let δ₀ : G.M.Pol B.ψ B.emb →ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    { toFun := d
      map_add' := fun f g => huniq _ _ _ (hd (f + g)) (fun x => by
        show HasDerivAt (fun t => T t ((f : SInf F (Fin a × Fin (a + a'))) + g) x) ((d f + d g) x) 0
        simp only [map_add, SchwartzMap.add_apply]
        exact (hd f x).add (hd g x))
      map_smul' := fun c f => huniq _ _ _ (hd (c • f)) (fun x => by simpa using (hd f x).const_mul c) }
  obtain ⟨δ, hδ⟩ := LinearMap.exists_extend δ₀
  have e : ∀ f (hf : f ∈ G.M.Pol B.ψ B.emb), δ f = d ⟨f, hf⟩ := fun f hf => by
    have := congrArg (fun φ => φ ⟨f, hf⟩) hδ
    exact this
  refine ⟨δ, fun f hf => ⟨by rw [e f hf]; exact hdP _, fun r hr x => ?_⟩⟩
  have h1 : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) = tens (evI F) (T t f) r :=
    fun t => hT' t f r hr
  simp only [h1]
  rw [e f hf]
  exact (hd ⟨f, hf⟩ _).mul_const (r x)

end GlobalTheory.OscLie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalOperatorThetaQuotientFinitePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LocalDescent

theorem descend {A A' P : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A'] [AddCommGroup P]
    [Module ℂ P] (S : Submodule ℂ A) (S' : Submodule ℂ A') (p : A →ₗ[ℂ] P) (p' : A' →ₗ[ℂ] P)
    (hp : S.map p = ⊤) (hp' : S'.map p' = ⊤) (r : A → A → Prop) (r' : A' → A' → Prop)
    (hex : ∀ x ∈ S, ∃ y ∈ S, r x y) (hex' : ∀ x ∈ S', ∃ y ∈ S', r' x y)
    (hlin : ∀ x ∈ S, ∀ z ∈ S, ∀ y w, r x y → r z w → ∀ s t : ℂ, r (s • x + t • z) (s • y + t • w))
    (heq : ∀ x ∈ S, ∀ x' ∈ S', ∀ y ∈ S, ∀ y' ∈ S', r x y → r' x' y' → p x = p' x' → p y = p' y') :
    ∃ T : Module.End ℂ P, (∀ x ∈ S, ∀ y ∈ S, r x y → p y = T (p x)) ∧
      ∀ x ∈ S', ∀ y ∈ S', r' x y → p' y = T (p' x) := by
  have hwd : ∀ x ∈ S, ∀ z ∈ S, ∀ y ∈ S, ∀ w ∈ S, r x y → r z w → p x = p z → p y = p w := by
    intro x hx z hz y hy w hw h1 h2 h3
    obtain ⟨x', hx', e⟩ : p x ∈ S'.map p' := hp' ▸ Submodule.mem_top
    obtain ⟨y', hy', h'⟩ := hex' x' hx'
    rw [heq x hx x' hx' y hy y' hy' h1 h' e.symm, heq z hz x' hx' w hw y' hy' h2 h' (h3.symm.trans e.symm)]
  have hsec : ∀ ξ : P, ∃ x ∈ S, ∃ y ∈ S, p x = ξ ∧ r x y := by
    intro ξ
    obtain ⟨x, hx, e⟩ : ξ ∈ S.map p := hp ▸ Submodule.mem_top
    obtain ⟨y, hy, h⟩ := hex x hx
    exact ⟨x, hx, y, hy, e, h⟩
  choose f hf g hg hfp hfg using hsec
  have hcomb : ∀ (ξ η : P) (s t : ℂ), p (g (s • ξ + t • η)) = s • p (g ξ) + t • p (g η) := by
    intro ξ η s t
    have := hwd _ (hf (s • ξ + t • η)) _ (add_mem (S.smul_mem s (hf ξ)) (S.smul_mem t (hf η))) _ (hg _) _
      (add_mem (S.smul_mem s (hg ξ)) (S.smul_mem t (hg η))) (hfg _)
      (hlin _ (hf ξ) _ (hf η) _ _ (hfg ξ) (hfg η) s t) (by rw [hfp, map_add, map_smul, map_smul, hfp, hfp])
    rw [this, map_add, map_smul, map_smul]
  let T : Module.End ℂ P :=
    { toFun := fun ξ => p (g ξ)
      map_add' := fun ξ η => by simpa using hcomb ξ η 1 1
      map_smul' := fun s ξ => by simpa using hcomb ξ ξ s 0 }
  refine ⟨T, fun x hx y hy h => ?_, fun x hx y hy h => ?_⟩
  · exact hwd x hx _ (hf (p x)) y hy _ (hg _) h (hfg _) (hfp _).symm
  · exact (heq _ (hf (p' x)) x hx _ (hg _) y hy (hfg _) h (hfp _)).symm

theorem acts_comb {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hex : ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T φ φ₁)
    {φ ψ φ₁ ψ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) (hψ : ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    (h₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T φ φ₁)
    (h₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T ψ ψ₁) (s t : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T (s • φ + t • ψ) (s • φ₁ + t • ψ₁) := by
  have hs : s • φ + t • ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) :=
    add_mem ((GlobalTheory.WeilM.SB _).smul_mem s hφ) ((GlobalTheory.WeilM.SB _).smul_mem t hψ)
  obtain ⟨χ, -, hχ⟩ := hex _ hs
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have e : ∀ α β : (κ → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (s • α + t • β) R =
      s • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) α R + t • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) β R := by
    intro α β
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have key : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) χ R =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (s • φ₁ + t • ψ₁) R := by
    rw [← hχ R (hR _ hs), e, map_add, map_smul, map_smul, h₁ R (hR φ hφ), h₂ R (hR ψ hψ), e]
  have hχe : χ = s • φ₁ + t • ψ₁ := by
    funext y
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    have hRz : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
      simpa using (hR φ hφ).1 0 _ hz
    have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (y i))
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
    exact mul_right_cancel₀ hR0 this
  rw [← hχe]
  exact hχ

theorem exists_localOp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a a' : ℕ)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ hv ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.W (GlobalTheory.AdelicU.evFin F v),
    ∃ T : Module.End ℂ (Rf.Pi v),
      (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, hv)) φ φ₁ → Rf.p v φ₁ = T (Rf.p v φ)) ∧
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, hv)) φ φ₁ → Rf.p' v φ₁ = T (Rf.p' v φ) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM v h hh
  have hex := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ Bs a a' Γ Xc om om' hM.triple v h hh
  have hex' := GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ Bs a a' Γ Xc om om' hM.triple v h hh
  exact descend _ _ (Rf.p v) (Rf.p' v) (hM.fin.onto v) (hM.fin.onto' v)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, h))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, h)))
    hex hex' (fun x hx z hz y w h1 h2 s t => acts_comb v (om (1, h)) hex hx hz h1 h2 s t) (hM.fin.equiv v h hh)

end GlobalTheory.LocalDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselPairedKernelHeightBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.PairKerBound

theorem kernel_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∃ (C : ℝ) (a : ℕ), ∀ h h₀ h₁, ‖contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0‖ ≤ C * (height J.W₀ h₀ * height B.A h₁ * height B.V h) ^ a := by
  intro D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.JacMean.xLast_lin B.d B.o B.line
  obtain ⟨C₁, A₁, hC₁⟩ := GlobalTheory.FlatSup.flat_sup_growth D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s x hx Φ hΦ
  obtain ⟨C₂, A₂, hC₂⟩ := GlobalTheory.SupThetaGrowth.om_sup_growth D ψ J.W₀ B.L χ χz omz homz Φ₀ hΦ₀
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le D J.W J.W₀ (σ + 1) J.d
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le D B.V B.V₀ σ B.d
  obtain ⟨C₅, a₅, hC₅⟩ := GlobalTheory.EmbHeight.height_emb_le D B.V₀ B.A B.L B.o
  have key : ∀ h h₀ h₁ w, s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ)) w =
      flatS J.d B.d s (rat x) 0 (s.om (J.d.emb0 h₀, embA B.d B.o h₁ * h) Φ) w := by
    intro h h₀ h₁ w
    have e := GlobalTheory.AscFlatEquiFB.flFB_equivariant D ψ σ J B s (s.om (1, h) Φ) (s.weil.om_pres _ _ hΦ) h₀ 1 (one_mem _) h₁
    have hp : psiBes ψ B.d 1 (vecB B.o B.ζ) 1 = 1 :=
      (GlobalTheory.MixPer.charLaws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1).2.1 _ 1 (one_mem _)
    rw [hp, star_one, one_smul, one_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one] at e
    rw [← e]
    show flatS J.d B.d s (xLast B.d (vecB B.o B.ζ)) 0 _ w = _
    rw [hxe]
  have hC₃1 : 1 ≤ C₃ := by simpa using (GlobalTheory.Grow.one_le_height J.W (J.d.emb0 1)).trans (hC₃ 1)
  have hC₄1 : 1 ≤ C₄ := by simpa using (GlobalTheory.Grow.one_le_height B.V (B.d.emb0 1)).trans (hC₄ 1)
  have hC₅1 : 1 ≤ C₅ := by simpa using (GlobalTheory.Grow.one_le_height B.V₀ (B.o.emb (1, 1))).trans (hC₅ 1)
  have hM₁ : 0 ≤ max C₁ 0 := le_max_right _ _
  have hM₂ : 0 ≤ max C₂ 0 := le_max_right _ _
  have hK : 0 ≤ C₃ * C₄ * C₅ := by positivity
  refine ⟨max C₁ 0 * (C₃ * C₄ * C₅) ^ A₁ * max C₂ 0, (a₅ + 2) * A₁ + A₂, fun h h₀ h₁ => ?_⟩
  have p0 : 1 ≤ height J.W₀ h₀ := GlobalTheory.Grow.one_le_height _ _
  have p1 : 1 ≤ height B.A h₁ := GlobalTheory.Grow.one_le_height _ _
  have p2 : 1 ≤ height B.V h := GlobalTheory.Grow.one_le_height _ _
  generalize hX : height J.W₀ h₀ * height B.A h₁ * height B.V h = X
  have n01 : 0 ≤ height J.W₀ h₀ * height B.A h₁ := mul_nonneg (by linarith) (by linarith)
  have q0 : height J.W₀ h₀ ≤ X := by
    rw [← hX]; exact (le_mul_of_one_le_right (by linarith) p1).trans (le_mul_of_one_le_right n01 p2)
  have q1 : height B.A h₁ ≤ X := by
    rw [← hX]; exact (le_mul_of_one_le_left (by linarith) p0).trans (le_mul_of_one_le_right n01 p2)
  have q2 : height B.V h ≤ X := by
    rw [← hX]; exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le p0 p1)
  have hX1 : 1 ≤ X := p2.trans q2
  have hX0 : 0 ≤ X := by linarith
  have e1 : height J.W (J.d.emb0 h₀) ≤ C₃ * X := (hC₃ h₀).trans (mul_le_mul_of_nonneg_left q0 (by linarith))
  have e2 : height B.V (embA B.d B.o h₁ * h) ≤ C₄ * C₅ * X ^ (a₅ + 1) := by
    have f1 : height B.V (embA B.d B.o h₁) ≤ C₄ * (C₅ * X ^ a₅) := by
      rw [embA_apply]
      refine (hC₄ _).trans (mul_le_mul_of_nonneg_left ((hC₅ h₁).trans ?_) (by linarith))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) q1 _) (by linarith)
    calc _ ≤ height B.V (embA B.d B.o h₁) * height B.V h := GlobalTheory.Grow.height_mul_le _ _ _
      _ ≤ (C₄ * (C₅ * X ^ a₅)) * X := mul_le_mul f1 q2 (by linarith) (by positivity)
      _ = C₄ * C₅ * X ^ (a₅ + 1) := by ring
  have hP : height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h) ≤ C₃ * C₄ * C₅ * X ^ (a₅ + 2) := by
    calc _ ≤ (C₃ * X) * (C₄ * C₅ * X ^ (a₅ + 1)) :=
          mul_le_mul e1 e2 (zero_le_one.trans (GlobalTheory.Grow.one_le_height _ _)) (by positivity)
      _ = _ := by ring
  have hf : ∀ w, ‖flatS J.d B.d s (rat x) 0 (s.om (J.d.emb0 h₀, embA B.d B.o h₁ * h) Φ) w‖ ≤
      max C₁ 0 * (C₃ * C₄ * C₅) ^ A₁ * X ^ ((a₅ + 2) * A₁) := by
    intro w
    have hP0 : 0 ≤ height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h) :=
      mul_nonneg (zero_le_one.trans (GlobalTheory.Grow.one_le_height _ _)) (zero_le_one.trans (GlobalTheory.Grow.one_le_height _ _))
    calc _ ≤ C₁ * (height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h)) ^ A₁ := hC₁ _ _ 0 w
      _ ≤ max C₁ 0 * (height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h)) ^ A₁ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hP0 _)
      _ ≤ max C₁ 0 * (C₃ * C₄ * C₅ * X ^ (a₅ + 2)) ^ A₁ :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP0 hP _) hM₁
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hg : ∀ v, ‖omz (h₀, 1) Φ₀ v‖ ≤ max C₂ 0 * X ^ A₂ := by
    intro v
    have := hC₂ h₀ 1 v
    rw [GlobalTheory.Grow.height_one, mul_one] at this
    refine this.trans ?_
    calc C₂ * height J.W₀ h₀ ^ A₂ ≤ max C₂ 0 * height J.W₀ h₀ ^ A₂ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) q0 _) hM₂
  unfold contractT thPair
  have hvol := vL.covol.2.2
  refine (norm_setIntegral_le_of_norm_le_const (C := max C₁ 0 * (C₃ * C₄ * C₅) ^ A₁ * X ^ ((a₅ + 2) * A₁) *
    (max C₂ 0 * X ^ A₂)) (by rw [hvol]; exact ENNReal.one_lt_top) fun v _ => ?_).trans ?_
  · beta_reduce
    rw [norm_mul, norm_star, key]
    exact mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)
  · rw [measureReal_def, hvol, ENNReal.toReal_one, mul_one, pow_add]
    exact le_of_eq (by ring)

end GlobalTheory.PairKerBound
end
end

