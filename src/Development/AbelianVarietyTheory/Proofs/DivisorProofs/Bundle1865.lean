import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEqualSignKernelsLargeConstants
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.RatTop

theorem exists_linearMap_of_repr_mem_range {K : Type} [Field K] (φ : K →+* ℂ) {VS VT WS WT : Type}
    [AddCommGroup VS] [Module K VS] [AddCommGroup VT] [Module K VT]
    [AddCommGroup WS] [Module ℂ WS] [AddCommGroup WT] [Module ℂ WT]
    (mS : VS →ₛₗ[φ] WS) (mT : VT →ₛₗ[φ] WT) {ι κ : Type} [Fintype ι] [Fintype κ]
    (b0 : Module.Basis ι K VS) (bS : Module.Basis ι ℂ WS) (bT : Module.Basis κ ℂ WT)
    (uS : ι → VS) (uT : κ → VT) (hS : ∀ i, mS (uS i) = bS i) (hT : ∀ k, mT (uT k) = bT k)
    (L : WS →ₗ[ℂ] WT) (hL : ∀ k i, bT.repr (L (bS i)) k ∈ Set.range φ) :
    ∃ f : VS →ₗ[K] VT, ∀ u, L (mS u) = mT (f u) := by
  classical
  haveI : FiniteDimensional K VS := Module.Finite.of_basis b0
  have hli : LinearIndependent K uS := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : ∑ i, φ (g i) • bS i = 0 := by
      have := congrArg mS hg
      simpa [map_sum, LinearMap.map_smulₛₗ, hS] using this
    have h2 := Fintype.linearIndependent_iff.mp bS.linearIndependent _ h1 i
    exact φ.injective (by rw [h2, map_zero])
  have hsp : Submodule.span K (Set.range uS) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis b0).symm
  let bS' : Module.Basis ι K VS := Module.Basis.mk hli hsp.ge
  choose m hm using hL
  let f : VS →ₗ[K] VT := bS'.constr K fun i => ∑ k, m k i • uT k
  refine ⟨f, fun u => ?_⟩
  have e : (L.comp mS : VS →ₛₗ[φ] WT) = (mT.comp f : VS →ₛₗ[φ] WT) := by
    refine bS'.ext fun i => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Module.Basis.constr_basis, Module.Basis.mk_apply, hS, map_sum]
    conv_lhs => rw [← bT.sum_repr (L (bS i))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smulₛₗ, hT, hm]
  exact LinearMap.congr_fun e u

end GlobalTheory.RatTop

namespace GlobalTheory.KerConjMean

theorem ratTopAt_big : BigC fun _ ch _ _ => RatTopAt ch := by
  refine ⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩⟩
  intro D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ hK
  intro Φ β d hd c j
  obtain ⟨hβ, τ, hτ, hdτ⟩ := hd
  have hr := (hK.isRatAt hβ hτ hdτ c).1 j
  refine GlobalTheory.RatTop.exists_linearMap_of_repr_mem_range D.what₂.embLL (GlobalTheory.CoefModel.mapVV D.what₂.embLL _)
    (GlobalTheory.CoefModel.mapVV D.what₂.embLL _) (bVV D.what₂.LL _) (bVV ℂ _) (bVV ℂ _)
    (fun i => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ i).choose_spec.1⟩)
    (fun k => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.1⟩) ?_ ?_ _ ?_
  · intro i
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ i).choose_spec.2).symm
  · intro k
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm
  · intro k i
    have h := hr k i
    rwa [Normal.kkIn, LinearMap.toMatrix_apply] at h

end GlobalTheory.KerConjMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidDescendsFieldMapStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_descends_field_map : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (F Ω : Type) [Field F] [Field Ω] (φ : F →+* Ω) (b : Sp F ⟶ S), RatRigid G (spMap φ ≫ b) → RatRigid G b := by
  first | exact @GlobalTheory.Nef.ratRigid_of_field_map | exact GlobalTheory.Nef.ratRigid_of_field_map | (intros; apply GlobalTheory.Nef.ratRigid_of_field_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsGaussianSmulConstUnique
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormExact

theorem reads_smul_const_unique : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (G : VC D a d → ℂ) (f : WO S T → ℂ) (c c' : ℂ), G ≠ 0 →
  Reads ψ θ hS hT cc δ r (c • G) f → Reads ψ θ hS hT cc δ r (c' • G) f → c = c' := by
  intro D ψ θ S T a d hS hT cc δ r hs G f c c' hG h1 h2
  subst hS hT
  obtain ⟨Y, hY⟩ : ∃ Y, G Y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hG (funext hc)
  have hδ : δ ≠ 0 := delta_ne_zero hs.crv
  have hr : r ≠ 0 := IsScale.ne_zero hs.crv.1.1 hs.scale
  have hm : ∀ τ, δ * embT D τ r ≠ 0 := fun τ => mul_ne_zero hδ ((map_ne_zero _).2 hr)
  obtain ⟨x, ⟨hx, hx0⟩, -⟩ := GlobalTheory.StdUnn.exists_unique_of_comp_finPart D θ hs.inf T.rank S.rank
    (fun τ => Matrix.of fun i j => Y τ i j / (δ * embT D τ r)) 0
  replace hx0 : x.map (finPart D) = 0 := by rw [hx0]; exact Matrix.map_zero _ (map_zero _)
  have hxY : coordY θ rfl rfl δ r x = Y := by
    funext τ i j
    simp only [coordY, Fin.cast_eq_self, hx, Matrix.of_apply]
    have hE : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    field_simp [hm τ, hE, hδ]
  have e1 := h1.2 x hx0
  have e2 := h2.2 x hx0
  rw [hxY] at e1 e2
  rw [e1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at e2
  have he := Complex.exp_ne_zero (-((Real.pi : ℂ) / 2) * Hf D (tor0 D cc δ) Y Y)
  have := mul_left_cancel₀ he e2
  exact mul_right_cancel₀ hY this

end GlobalTheory.NormExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedFamilyTripleExists
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

noncomputable section

namespace GlobalTheory.SmallTriple

open GlobalTheory.Grid MeasureTheory

variable {D : D7}

private theorem eta_sq_eq_one {η : (AF D.host.F)ˣ →* Circle} (h : IsEta D η) (a : (AF D.host.F)ˣ) : η a ^ 2 = 1 := by
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have e := h.2.2.1 (idF D a)
  have e2 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := by
    ext1
    show Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) (a : AF D.host.F)) = ((a ^ 2 : (AF D.host.F)ˣ) : AF D.host.F)
    let b := (Module.finBasis D.host.F D.host.E).baseChange (AF D.host.F)
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin, h2, Units.val_pow_eq_pow_val]
  rwa [e2, map_pow] at e

private theorem resEta_of_add_two {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ (n + 2)) : ResEta D χ n :=
  ⟨h.1, fun η hη a => by rw [h.2 η hη a, pow_add, eta_sq_eq_one hη, mul_one]⟩

private theorem exists_isWeil (hP : GlobalTheory.Published.WeilRepresentationUnitaryPair) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (ε : Bool) (S W : HSp D) {χS χW : (AE D)ˣ →* Circle} (h1 : IsHeckeChar D χS) (h2 : IsHeckeChar D χW)
    (h3 : ResEta D χS S.rank) (h4 : ResEta D χW W.rank) : ∃ ω : WRep S W, IsWeil ψ ε S W χS χW ω := by
  obtain ⟨om, h⟩ := hP D ψ (sgn ε S) W χS χW hψ h1 h2 h3 h4
  exact ⟨om.comp ((ofSgn ε S).symm.toMonoidHom.prodMap (MonoidHom.id _)), h⟩

private theorem exists_vac (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) : ∃ f, IsVacO ψ θ S T sS sT ΛS ΛT f := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T sS sT hS hT ΛS ΛT dS dT
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  let _ : MeasurableSpace (WO S T) := measMx _ _
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have h1 := (hf 1).1
  simp only [one_mul] at h1
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.T.exists_normalise_meanSquare_of_cocompact' (WO S T) (ratL T S) K hK hcov f h1.cont f0 (by
    rintro _ ⟨g, rfl⟩ w
    have e := h1.quasi g w
    have e' := congrArg norm e
    rw [norm_mul, hψ.1.2.1, one_mul] at e'
    exact e')
  exact ⟨fun w => c * f w, hψ, hθ, (hf c).1, (hf c).2.1, (hf c).2.2, ⟨(μ, 𝓕), hμ⟩,
    fun p hp => hc p.1 p.2 hp.1 hp.2.1 hp.2.2⟩

private theorem exists_tri : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (T : Type) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E)
    (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)) (rB : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig B') (rW : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig WW₁),
    IsInfFam θ → X.Is ψ θ α β νH S → rB.Is → rW.Is → B'.rank + 2 = A'.rank → WW₁.rank + 2 = WW.rank →
    ∃ Y : Tri T A B' WW₁, Y.rA = X.rA ∧ Y.rA' = rB ∧ Y.rW = rW ∧ Y.Is ψ θ α β νH S := by
  intro hP D T A A' WW B' WW₁ X ψ θ α β νH S rB rW hθ hX hB hW eB eW
  have hψ : IsStdChar D ψ (-1) := hX.isVac.1
  have hA := hX.rigA
  choose ω hω using fun t => exists_isWeil hP.weilRepresentationUnitaryPair hψ true A WW₁ (hX.weil t).hecS (hX.weil t).hecT
    (hX.weil t).resS (resEta_of_add_two (eW ▸ (hX.weil t).resT))
  choose ω' hω' using fun t => exists_isWeil hP.weilRepresentationUnitaryPair hψ false B' WW₁ (hX.weil' t).hecS (hX.weil' t).hecT
    (resEta_of_add_two (eB ▸ (show ResEta D (α t) A'.rank from (hX.weil' t).resS))) (resEta_of_add_two (eW ▸ (hX.weil' t).resT))
  have hneg : IsSelfDualC (neg A) X.rA.Λ := by
    refine ⟨hA.1.1, fun y => (hA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  obtain ⟨vac, hv⟩ := exists_vac ψ θ hψ hθ (neg A) WW₁ (fun τ => -X.rA.s τ) rW.s
    (fun τ => isCartanInv_sgn true _ τ (hA.2.2 τ).1) (fun τ => (hW.2.2 τ).1) X.rA.Λ rW.Λ hneg hW.1
  obtain ⟨vac', hv'⟩ := exists_vac ψ θ hψ hθ B' WW₁ rB.s rW.s
    (fun τ => (hB.2.2 τ).1) (fun τ => (hW.2.2 τ).1) rB.Λ rW.Λ hB.1 hW.1
  have hν : ∀ t, IsHeckeChar D (α t / β t) := fun t => (hX.weil' t).hecT
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D ψ θ A WW₁ X.rA rW _ _ _ _ _ hA hW (hν t) (hX.idem t)
    (GlobalTheory.ConstRatio.ideal_ne_bot X S t) hv
  choose f' hf' _ using fun t => GlobalTheory.T.exists_thetaFunction_standardPairSecond D ψ θ B' WW₁ rB rW _ _ _ _ A.rank _ hB hW (hν t) (hX.idem t)
    (GlobalTheory.ConstRatio.ideal_ne_bot X S t) hv'
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas B'
  have hr := hX.rank
  exact ⟨⟨X.rA, rB, rW, ω, ω', vac, vac', X.e, X.c, f, f', X.m, X.fd, m', fd'⟩, rfl, rfl, rfl,
    ⟨by omega, hA, hB, hW, hω, hω', hv, hv', hX.idem, hX.expo, hf, hf', hX.meas, hm'⟩⟩

end GlobalTheory.SmallTriple

end

theorem _root_.GlobalTheory.T.rigidified_family_triple_exists : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (T : Type) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E)
    (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)) (rB : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig B') (rW : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig WW₁),
    IsInfFam θ → X.Is ψ θ α β νH S → rB.Is → rW.Is → B'.rank + 2 = A'.rank → WW₁.rank + 2 = WW.rank →
    ∃ Y : Tri T A B' WW₁, Y.rA = X.rA ∧ Y.rA' = rB ∧ Y.rW = rW ∧ Y.Is ψ θ α β νH S := GlobalTheory.SmallTriple.exists_tri
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RouteBigVertexKernelProductEqConstMulThetaKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid
noncomputable section

namespace GlobalTheory.RouteSeesaw

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.MixModel

theorem data_theta {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)}
    (hΘ : IsMatched B t ρ i j Θ Θ') : ∀ d ∈ Θ.support,
      IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, -, φ₁, φ₂, hloc, -⟩, rfl, -⟩ := hΘ
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
  have v1 := (ρ.vX_is (i : ℕ) ((j : ℕ) + 1) i.2 j.2).2.theta
  have v2 := (ρ.vT_is t ((i : ℕ) + 1) (j : ℕ) i.2 j.2).2.theta
  have t1 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h1.2 v1
  have t2 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h2.2 v2
  exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩

theorem dagger_zero {D : D7} (S T : HSp D) : dagger S T 0 = 0 := by
  simp [dagger]

theorem hecke_mul' {D : D7} {χ ν : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hν : IsHeckeChar D ν) :
    IsHeckeChar D (χ * ν) :=
  ⟨hχ.1.mul hν.1, fun x => by rw [MonoidHom.mul_apply, hχ.2, hν.2, mul_one]⟩

theorem splitFac_ratio {D : D7} (a b c : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) :
    (splitFacO a c⁻¹ x y : ℂ) * (splitFacO b⁻¹ c⁻¹ x y : ℂ)⁻¹ = ((a y * b y : Circle) : ℂ) := by
  simp only [splitFacO, MonoidHom.inv_apply, inv_inv, Circle.coe_mul, Circle.coe_inv]
  have h1 : ((c x : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have h2 : ((b y : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  field_simp

theorem seesaw_product {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {Wo V V₁ : HSp D}
    {c1S c1T c2S c2T : (AE D)ˣ →* Circle}
    {ω₁ : GA D (negSp Wo) × GA D V →* Module.End ℂ (WO (negSp Wo) V → ℂ)}
    {ω₂ : GA D V₁ × GA D Wo →* Module.End ℂ (WO V₁ Wo → ℂ)}
    (H1 : IsWeilDatumO ψ (negSp Wo) V c1S c1T ω₁) (H2 : IsWeilDatumO ψ V₁ Wo c2S c2T ω₂)
    {f₁ : WO (negSp Wo) V → ℂ} {f₂ : WO V₁ Wo → ℂ} (hf₁ : IsThetaFunO ψ (negSp Wo) V f₁)
    (hf₂ : IsThetaFunO ψ V₁ Wo f₂) (g : GA D V) (g₁ : GA D V₁) :
    ∃ (X : HSp D) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep Wo X), IsWeil ψ true Wo X χ χ' ω ∧
      X.rank = V.rank + V₁.rank ∧ ∃ Φ : WO (sgn true Wo) X → ℂ, IsThetaFunO ψ (sgn true Wo) X Φ ∧
        ∃ (h : GA D X) (c : ℂ), ∀ u, ω₁ (negGA Wo u, g) f₁ 0 * ω₂ (g₁, u) f₂ 0 = c * thetaKO ω u h Φ := by
  have hη : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η :=
    (GlobalTheory.Mem.EtaTilde.exists_etaTilde D).imp fun _ h => ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩

  have H2b : IsWeilDatumO ψ (negSp Wo) V₁ c2T⁻¹ c2S⁻¹ (conjSource (conjAdjoint ω₂)) :=
    GlobalTheory.ConjWeil.weil_conjSource D ψ Wo V₁ _ _ _ (GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ V₁ Wo _ _ ω₂ H2)

  obtain ⟨ω₂c, H2c⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ (negSp Wo) V₁ c1S c2S⁻¹ hη H1.hecS
    (GlobalTheory.ConjWeil.hecke_inv H2.hecS) H1.resS (resEta_inv H2.resS)

  obtain ⟨ω', H'⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ (negSp Wo) (GlobalTheory.Doubling.hsum V V₁) c1S (c1T * c2S⁻¹) hη
    H1.hecS (hecke_mul' H1.hecT (GlobalTheory.ConjWeil.hecke_inv H2.hecS)) H1.resS (resEta_mul H1.resT (resEta_inv H2.resS))
  set o := GlobalTheory.OrthSumExists.orthDecHsum D V V₁ with ho
  have TT := GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ (GlobalTheory.Doubling.hsum V V₁) V V₁ o (negSp Wo)

  have hF₂ : IsThetaFunO ψ (negSp Wo) V₁ (cj id (cj (dagger Wo V₁) f₂)) := by
    have h1 : IsThetaFunO ψ Wo V₁ (cj (dagger Wo V₁) f₂) := ((GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ V₁ Wo).2.2.1 f₂).2 hf₂
    have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hψ Wo V₁
    exact ((I.1 _).2).2 h1
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D V₁ g₁
  let ω : WRep Wo (GlobalTheory.Doubling.hsum V V₁) := ω'.comp ((negGA Wo).toMonoidHom.prodMap (MonoidHom.id _))
  have hω : ω.toSgn true = ω' := MonoidHom.ext fun p => rfl
  refine ⟨GlobalTheory.Doubling.hsum V V₁, c1S, c1T * c2S⁻¹, ω, ?_, rfl, o.boxT (negSp Wo) f₁ (cj id (cj (dagger Wo V₁) f₂)),
    TT.box_theta _ _ hf₁ hF₂, o.emb (g, g₁), ((c1S y * c2T y : Circle) : ℂ)⁻¹, fun u => ?_⟩
  · show IsWeilDatumO ψ (sgn true Wo) _ _ _ (ω.toSgn true)
    rw [hω]; exact H'
  · obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D (negSp Wo) (negGA Wo u)
    have k1 := TT.om_box c1S c1T c2S⁻¹ ω' ω₁ ω₂c H' H1 H2c (negGA Wo u) g g₁ f₁ _ hf₁ hF₂
    have k2 := GlobalTheory.WeilChange.weilData_differ_by_splitFac D ψ (negSp Wo) V₁ c2T⁻¹ c2S⁻¹ c1S c2S⁻¹ _ ω₂c H2b H2c
      (negGA Wo u) g₁ x y hx hy _ hF₂
    have k3 : conjSource (conjAdjoint ω₂) (negGA Wo u, g₁) (cj id (cj (dagger Wo V₁) f₂)) 0 = ω₂ (g₁, u) f₂ 0 := by
      rw [GlobalTheory.ConjWeil.conjSource_apply]
      simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
      rw [GlobalTheory.TensorTargetRule.conjAdjoint_cj]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_zero]
    show _ = _ * ω' (negGA Wo u, o.emb (g, g₁)) (o.boxT (negSp Wo) f₁ (cj id (cj (dagger Wo V₁) f₂))) 0
    rw [k1, OrthDec.boxT_zero, k2, Pi.smul_apply, smul_eq_mul, k3, splitFac_ratio]
    have h0 : ((c1S y * c2T y : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    field_simp

end GlobalTheory.RouteSeesaw

open GlobalTheory.RouteSeesaw in

theorem GlobalTheory.FunObj.routeBig_kernel_product_eq_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ'),
    ∀ d ∈ Θ.support, ∀ (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))),
      ∃ (ε : Bool) (X : HSp D) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep (G.V (.grid (i + 1) (j + 1))) X),
        IsWeil W.ψ ε _ X χ χ' ω ∧ X.rank = (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank ∧
        ∃ Φ : WO (sgn ε (G.V (.grid (i + 1) (j + 1)))) X → ℂ, IsThetaFunO W.ψ (sgn ε _) X Φ ∧
          ∃ (h : GA D X) (c : ℂ), ∀ u, W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁ =
            c * thetaKO ω u h Φ := by
  intro D T L sc G μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ d hd g g₁
  obtain ⟨hf₁, hf₂⟩ := data_theta W B ρ t i j hΘ d hd
  have hp1 : (Pair.chi (i : ℕ) ((j : ℕ) + 1) : Pair T).InRange D.R.m := ⟨by omega, by omega⟩
  have hp2 : (Pair.mu t ((i : ℕ) + 1) (j : ℕ)).InRange D.R.m := ⟨by omega, by omega⟩
  obtain ⟨X, χ, χ', ω, hω, hX, Φ, hΦ, h, c, hc⟩ :=
    seesaw_product W.ψ_std (W.om_is _ hp1) (W.om_is _ hp2) hf₁ hf₂ g g₁
  exact ⟨true, X, χ, χ', ω, hω, hX, Φ, hΦ, h, c, hc⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeFourierInvariant
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
namespace GlobalTheory.SchrCharPure

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
    ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ x, f' x = Complex.exp (-(2 * Real.pi * Complex.I) *
          ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (b i)) : ℝ) : ℂ)) * f x) →
      schr ψ (0, fun i => algebraMap F (AF F) (b i))
          (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)))) =
        pureA F f' ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ))) := by
  intro F _ _ ψ hψ κ _ a ha b hb f f' hf'
  funext x
  simp only [schr, pureA, add_zero, zero_dotProduct, mul_zero]
  rw [hf']
  by_cases hz : (fun i => (x i).2) ∈ GlobalTheory.EvAdm.scaledInt F κ a
  · rw [Set.indicator_of_mem (s := (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F))) hz]
    set u : AF F := x ⬝ᵥ fun i => algebraMap F (AF F) (b i) with hu
    have hsplit : u = (show AF F from (u.1, 0)) + (show AF F from (0, u.2)) := by
      show u = ((u.1 + 0, 0 + u.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
      rw [add_zero, zero_add]
      rfl
    have hu2 : u.2 = ∑ i, (x i).2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i) := by
      have e : u.2 = (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) u := rfl
      rw [e, hu, dotProduct]
      exact (map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => x i * algebraMap F (AF F) (b i)) Finset.univ).trans
        (Finset.sum_congr rfl fun i _ => rfl)
    have hu1 : u.1 = ∑ i, (x i).1 * algebraMap F (InfiniteAdeleRing F) (b i) := by
      have e : u.1 = (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) u := rfl
      rw [e, hu, dotProduct]
      exact (map_sum (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => x i * algebraMap F (AF F) (b i)) Finset.univ).trans
        (Finset.sum_congr rfl fun i _ => rfl)
    have hfin : ψ (show AF F from (0, u.2)) = 1 := by
      have := GlobalTheory.T.scaled_lattice_character_trivial F ψ hψ κ a ha b hb _ hz
      rw [← hu2] at this
      exact this
    have hAt : At (evI F) (show AF F from (u.1, 0)) := by
      intro w hw
      have h1 : w.1 = 0 := by
        have : InfiniteAdeleRing.ringEquiv_mixedSpace F w.1 = 0 := hw
        exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
      show ((w.1 * u.1, w.2 * 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
      rw [h1, zero_mul, mul_zero]
    have hinf := hψ.2.2 _ hAt
    have hev : evI F (show AF F from (u.1, 0)) = ∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * mixedEmbedding F (b i) := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = _
      rw [hu1, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, map_mul]
    rw [hsplit, AddChar.map_add_eq_mul, hfin, hinf, hev]
    ring
  · rw [Set.indicator_of_notMem (s := (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F))) hz]
    simp

end GlobalTheory.SchrCharPure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPureStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_adelic_eq_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    schA F κ = Submodule.span ℂ {Φ | ∃ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) ∧
      (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) ∧ Φ = pure f φ} := by
  first | exact @GlobalTheory.WeylSpan.schA_eq_span_pure | exact GlobalTheory.WeylSpan.schA_eq_span_pure | (intros; apply GlobalTheory.WeylSpan.schA_eq_span_pure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzMap_barrelledSpace' : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V], BarrelledSpace ℂ (SchwartzMap V ℂ) := by
  first | exact @GlobalTheory.schwartzMap_barrelledSpace | exact GlobalTheory.schwartzMap_barrelledSpace | (intros; apply GlobalTheory.schwartzMap_barrelledSpace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInvariantVectorStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_invariant_vector : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
    ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v), c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ η : κ → Fv F v, (∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψ (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ := by
  first | exact @GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any | exact GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any | (intros; apply GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any <;> assumption)
end

