import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3388
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3389
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverByPolarizationPowerSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreIsAbelianSchemeRelDimOfFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_isAbelianScheme_relDim_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → IsAbelianScheme A ∧ SmoothOfRelativeDimension n A.hom := by
  first | exact @GlobalTheory.FibreAbDim.isAbelianScheme_and_relDim | exact GlobalTheory.FibreAbDim.isAbelianScheme_and_relDim | (intros; apply GlobalTheory.FibreAbDim.isAbelianScheme_and_relDim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSignatureSumEqTwiceDimensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmType_signature_sum_eq_twice_dimension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ), ∑ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) * (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) = 2 * (Module.finrank ℚ E / 2 * p * q) := by
  first | exact @GlobalTheory.BalProj.signature_count | exact GlobalTheory.BalProj.signature_count | (intros; apply GlobalTheory.BalProj.signature_count <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceClosedFibreModificationFieldExtensStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedSpace_closedFibre_modification_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) := by
  first | exact @GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field | exact GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field | (intros; apply GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspValueLePhiComplement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp

set_option maxHeartbeats 2000000 in

theorem exists_cusp_value_le_phi : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ w : space TF.X Z Y.U la, evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 ∧ (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) ≤ φT / 2500 := by
  intro h1 h2 h3 h4
  refine ((((GlobalTheory.T.jet_number_weight_set h1 h2 h3 h4).and (GlobalTheory.T.jet_number_upper_weight h3)).and (GlobalTheory.T.weight_parameter_strict_antitone h3)).and ((GlobalTheory.T.jet_number_quotient_bounds h3).and h3)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C, hC, x0, hJ⟩, ⟨C1, hC1, x1, hN⟩⟩, ⟨C2, hC2, x2, hA⟩⟩, ⟨⟨C3, hC3, x3, hB⟩, ⟨C4, hC4, x4, hS⟩⟩⟩ := h
  refine ⟨C, hC, max (max x0 x1) (max x2 (max x3 x4)), fun x hx' hle ι p hp i hi Y hY Z TF la hla y hy T io y' g φT hg hφT hpt => ?_⟩
  have l0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have l1 : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have l2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
  have l3 : x3 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hle
  have l4 : x4 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hle
  obtain ⟨-, -, hfin, hquo, -⟩ := hA x hx' l2 ι p hp i hi
  obtain ⟨⟨u1, hu1⟩, -⟩ := (hS x hx' l4 ι p hp i).2.2.2.2.2.2 hi
  have hnum : GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) (1 / 2500) := by
    rcases hla with rfl | hla
    · have := (hB x hx' l3 ι p hp i hi u1 hu1).1
      rwa [hquo u1 hu1] at this
    · rw [Set.mem_singleton_iff] at hla
      subst hla
      exact hN x hx' l1 ι p hp i hi
  obtain ⟨f, hf0, hfb⟩ := hJ x hx' l0 ι p hp i hi Y hY Z TF la hla (1 / 2500) hnum y hy T io y' g φT hg hφT hpt
  have hE : Extends TF.X Z Y.U la := GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace (Fm.D x ι) p.T.toCore ((i : ℕ) + 1) Y _ _ hY.1 hfin Z TF la
  refine ⟨hE.equiv f, ?_⟩
  have e : ofSpace TF.X Z Y.U la (hE.equiv f) = f := hE.equiv.symm_apply_apply f
  rw [e]
  refine ⟨hf0, ?_⟩
  rw [div_eq_mul_one_div, mul_comm]
  exact hfb

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseAffineChartPreimageInteriorStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_affineChart_preimage_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens), Dense ((chart U).base ⁻¹' (interior Y : Set Y.X)) := by
  first | exact @GlobalTheory.BalProj.chart_dense_interior | exact GlobalTheory.BalProj.chart_dense_interior | (intros; apply GlobalTheory.BalProj.chart_dense_interior <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelPersistsThetaSetupTowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividingLabel_persists_thetaSetupTower : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ := by
  first | exact @GlobalTheory.Poinc.Sep.Tower.div_lam | exact GlobalTheory.Poinc.Sep.Tower.div_lam | (intros; apply GlobalTheory.Poinc.Sep.Tower.div_lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveDivisorPosDegreeAmpleClassStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effectiveDivisor_pos_degree_ampleClass : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left), IsAmpleCls c → ∀ (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), Out.nonzeroLocus s ≠ ⊥ → Out.nonzeroLocus s ≠ ⊤ → 0 < inter A (Fin.cons (cls M hM) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  first | exact @GlobalTheory.AV.EffPos.inter_cons_pos | exact GlobalTheory.AV.EffPos.inter_cons_pos | (intros; apply GlobalTheory.AV.EffPos.inter_cons_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenRankInteriorEqSignatureStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenRank_interior_eq_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (𝔭 : PrimeSpectrum Γ(Y.X, U.1)), (chart U).base 𝔭 ∈ (interior Y : Set Y.X) → ∀ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) 𝔭.asIdeal.ResidueField) A (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ) = if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q := by
  first | exact @GlobalTheory.BalProjInt.eigRank_interior | exact GlobalTheory.BalProjInt.eigRank_interior | (intros; apply GlobalTheory.BalProjInt.eigRank_interior <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsPartValueTranslateProdTangents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EpsAdd

open GlobalTheory.VertSpanZero

variable {S : Type} [CommRing S]

abbrev R2 (S : Type) [CommRing S] := DualNumber (DualNumber S)

def mergeHom (S : Type) [CommRing S] : R2 S →+* DualNumber S where
  toFun z := z.fst + TrivSqZeroExt.inr z.snd.fst
  map_one' := by ext <;> simp
  map_mul' := by
    intro x y
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul] <;> ring
  map_zero' := by ext <;> simp
  map_add' := by intro x y; ext <;> simp <;> ring

def dmap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) : DualNumber A →+* DualNumber B where
  toFun z := TrivSqZeroExt.inl (φ z.fst) + TrivSqZeroExt.inr (φ z.snd)
  map_one' := by ext <;> simp
  map_mul' := by
    intro x y
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul] <;> ring
  map_zero' := by ext <;> simp
  map_add' := by intro x y; ext <;> simp <;> ring

@[simp] theorem dmap_fst {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z : DualNumber A) :
    (dmap φ z).fst = φ z.fst := by simp [dmap]

@[simp] theorem dmap_snd {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z : DualNumber A) :
    (dmap φ z).snd = φ z.snd := by simp [dmap]

@[simp] theorem mergeHom_fst (z : R2 S) : (mergeHom S z).fst = z.fst.fst := by simp [mergeHom]

@[simp] theorem mergeHom_snd (z : R2 S) : (mergeHom S z).snd = z.fst.snd + z.snd.fst := by simp [mergeHom]

def ovHom {X : Scheme.{0}} (x : Sp S ⟶ X) {A B : Type} [CommRing A] [CommRing B] (a : S →+* A) (b : S →+* B)
    (φ : A →+* B) (h : φ.comp a = b) : Over.mk (spMap b ≫ x) ⟶ Over.mk (spMap a ≫ x) :=
  Over.homMk (spMap φ) (by
    change spMap φ ≫ spMap a ≫ x = spMap b ≫ x
    rw [← Category.assoc, ← spMap_comp_eq, h])

theorem spMap_comp_eq_id {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (ψ : B →+* A)
    (h : φ.comp ψ = RingHom.id B) : spMap φ ≫ spMap ψ = 𝟙 _ := by
  rw [← spMap_comp_eq, h]
  show Spec.map (CommRingCat.ofHom (RingHom.id B)) = _
  rw [CommRingCat.ofHom_id, Spec.map_id]

end GlobalTheory.EpsAdd

namespace GlobalTheory.EpsAdd

open GlobalTheory.VertSpanZero

variable {S : Type} [CommRing S]

theorem snd_valR_mul_mul {X : Scheme.{0}} {G : Over X} [GrpObj G] (g : Sp S ⟶ G.left)
    (g' : tEpsG (g ≫ G.hom) ⟶ G) (hg' : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g)
    (p q : tEpsG (g ≫ G.hom) ⟶ G) (hp : redOver (g ≫ G.hom) ≫ p = 1) (hq : redOver (g ≫ G.hom) ≫ q = 1)
    (O : G.left.Opens) (hO : ⊤ ≤ g ⁻¹ᵁ O) (f : Γ(G.left, O)) :
    (valR (g' * (p * q)).left O f).snd = (valR (g' * p).left O f).snd + (valR (g' * q).left O f).snd := by
  let x := g ≫ G.hom
  let α := algebraMap S (DualNumber S)
  let i₁ : DualNumber S →+* R2 S := TrivSqZeroExt.inlHom (DualNumber S) (DualNumber S)
  let i₂ : DualNumber S →+* R2 S := dmap α
  let j : S →+* R2 S := i₁.comp α
  let fs : DualNumber S →+* S := (TrivSqZeroExt.fstHom S S S).toRingHom
  let r₁ : R2 S →+* DualNumber S := (TrivSqZeroExt.fstHom (DualNumber S) (DualNumber S) (DualNumber S)).toRingHom
  let r₂ : R2 S →+* DualNumber S := dmap fs
  have hi₂ : i₂.comp α = j := by ext s <;> simp [i₂, i₁, j, α, TrivSqZeroExt.algebraMap_eq_inl]
  have hm : (mergeHom S).comp j = α := by ext s <;> simp [i₁, j, α, TrivSqZeroExt.algebraMap_eq_inl]
  have hr₁ : r₁.comp j = α := by ext s <;> simp [r₁, i₁, j, α, TrivSqZeroExt.algebraMap_eq_inl]
  have hr₂ : r₂.comp j = α := by ext s <;> simp [r₂, fs, i₁, j, α, TrivSqZeroExt.algebraMap_eq_inl]
  let K₁ : Over.mk (spMap j ≫ x) ⟶ tEpsG x := ovHom x α j i₁ rfl
  let K₂ : Over.mk (spMap j ≫ x) ⟶ tEpsG x := ovHom x α j i₂ hi₂
  let M : tEpsG x ⟶ Over.mk (spMap j ≫ x) := ovHom x j α (mergeHom S) hm
  let R₁ : tEpsG x ⟶ Over.mk (spMap j ≫ x) := ovHom x j α r₁ hr₁
  let R₂ : tEpsG x ⟶ Over.mk (spMap j ≫ x) := ovHom x j α r₂ hr₂
  let C : Over.mk (spMap j ≫ x) ⟶ G := Over.homMk (spMap j ≫ g) (Category.assoc _ _ _)
  let φ : tEpsG x ⟶ Over.mk x := Over.homMk (spMap α) rfl
  let P : Over.mk (spMap j ≫ x) ⟶ G := C * ((K₁ ≫ p) * (K₂ ≫ q))
  have hC : ∀ (ρ : R2 S →+* DualNumber S) (h : ρ.comp j = α), ovHom x j α ρ h ≫ C = g' := fun ρ h =>
    Over.OverMorphism.ext (by
      change spMap ρ ≫ spMap j ≫ g = g'.left
      rw [hg', ← Category.assoc, ← spMap_comp_eq, h])
  have hid : ∀ (ρ : R2 S →+* DualNumber S) (h : ρ.comp j = α) (κ : DualNumber S →+* R2 S) (h' : κ.comp α = j),
      ρ.comp κ = RingHom.id _ → ovHom x j α ρ h ≫ ovHom x α j κ h' = 𝟙 _ := fun ρ h κ h' e =>
    Over.OverMorphism.ext (by
      change spMap ρ ≫ spMap κ = 𝟙 _
      exact spMap_comp_eq_id ρ κ e)
  have hred : ∀ (ρ : R2 S →+* DualNumber S) (h : ρ.comp j = α) (κ : DualNumber S →+* R2 S) (h' : κ.comp α = j),
      ρ.comp κ = α.comp fs → ovHom x j α ρ h ≫ ovHom x α j κ h' = φ ≫ redOver x := fun ρ h κ h' e =>
    Over.OverMorphism.ext (by
      change spMap ρ ≫ spMap κ = spMap α ≫ spMap fs
      rw [← spMap_comp_eq, ← spMap_comp_eq, e])
  have hMK₁ : M ≫ K₁ = 𝟙 _ := hid _ hm _ rfl (by ext s <;> simp [i₁])
  have hMK₂ : M ≫ K₂ = 𝟙 _ := hid _ hm _ hi₂ (by ext s <;> simp [i₂, α, TrivSqZeroExt.algebraMap_eq_inl])
  have hR₁K₁ : R₁ ≫ K₁ = 𝟙 _ := hid _ hr₁ _ rfl (by ext s <;> simp [r₁, i₁])
  have hR₁K₂ : R₁ ≫ K₂ = φ ≫ redOver x :=
    hred _ hr₁ _ hi₂ (by ext s <;> simp [r₁, i₂, fs, α, TrivSqZeroExt.algebraMap_eq_inl])
  have hR₂K₁ : R₂ ≫ K₁ = φ ≫ redOver x :=
    hred _ hr₂ _ rfl (by ext s <;> simp [r₂, i₁, fs, α, TrivSqZeroExt.algebraMap_eq_inl])
  have hR₂K₂ : R₂ ≫ K₂ = 𝟙 _ := hid _ hr₂ _ hi₂ (by ext s <;> simp [r₂, i₂, fs, α, TrivSqZeroExt.algebraMap_eq_inl])
  have eM : M ≫ P = g' * (p * q) := by
    simp only [P, comp_mul]
    rw [hC, ← Category.assoc M K₁, ← Category.assoc M K₂, hMK₁, hMK₂, Category.id_comp, Category.id_comp]
  have e1 : R₁ ≫ P = g' * p := by
    simp only [P, comp_mul]
    rw [hC, ← Category.assoc R₁ K₁, ← Category.assoc R₁ K₂, hR₁K₁, hR₁K₂, Category.id_comp,
      Category.assoc, hq, comp_one, _root_.mul_one]
  have e2 : R₂ ≫ P = g' * q := by
    simp only [P, comp_mul]
    rw [hC, ← Category.assoc R₂ K₁, ← Category.assoc R₂ K₂, hR₂K₁, hR₂K₂, Category.id_comp,
      Category.assoc, hp, comp_one, _root_.one_mul]
  have hgp : spMap fs ≫ (g' * p).left = g := by
    change (redOver x ≫ (g' * p)).left = g
    rw [comp_mul, hp, _root_.mul_one]
    change spMap fs ≫ g'.left = g
    rw [hg', ← Category.assoc, spMap_fst_algebraMap, Category.id_comp]
  have hP1 : spMap r₁ ≫ P.left = (g' * p).left := by rw [← e1]; rfl
  have hPO : ⊤ ≤ P.left ⁻¹ᵁ O := GlobalTheory.CechKS.le_preimage_of_red hP1 (GlobalTheory.CechKS.le_preimage_of_red hgp hO)
  rw [← eM, ← e1, ← e2]
  change (valR (spMap (mergeHom S) ≫ P.left) O f).snd =
    (valR (spMap r₁ ≫ P.left) O f).snd + (valR (spMap r₂ ≫ P.left) O f).snd
  rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hPO f, GlobalTheory.Points.valR_spMap_comp _ _ _ hPO f,
    GlobalTheory.Points.valR_spMap_comp _ _ _ hPO f]
  simp [r₁, r₂, fs]

end GlobalTheory.EpsAdd

namespace GlobalTheory.EpsAdd

open GlobalTheory.VertSpanZero

theorem snd_valR_mul_prod : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (S : Type) [CommRing S] (g : Sp S ⟶ G.left)
    (g' : tEpsG (g ≫ G.hom) ⟶ G), g'.left = spMap (algebraMap S (DualNumber S)) ≫ g →
    ∀ (n : ℕ) (u : Fin n → (tEpsG (g ≫ G.hom) ⟶ G)),
    (∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left = (1 : Over.mk (g ≫ G.hom) ⟶ G).left) →
    ∀ (O : G.left.Opens), ⊤ ≤ g ⁻¹ᵁ O → ∀ f : Γ(G.left, O),
    (valR (g' * (List.ofFn u).prod).left O f).snd = ∑ a, (valR (g' * u a).left O f).snd := by
  intro X G _ S _ g g' hg' n
  induction n with
  | zero =>
    intro u _ O hO f
    rw [List.ofFn_zero, List.prod_nil, _root_.mul_one, hg', GlobalTheory.Points.valR_spMap_comp _ _ _ hO f]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  | succ n ih =>
    intro u hu O hO f
    have hu' : ∀ a, redOver (g ≫ G.hom) ≫ u a = 1 := fun a => Over.OverMorphism.ext (hu a)
    have hrest : redOver (g ≫ G.hom) ≫ (List.ofFn fun i : Fin n => u i.succ).prod = 1 := by
      refine redOver_comp_prod _ _ fun w hw => ?_
      obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ w).1 hw
      exact hu' _
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ,
      snd_valR_mul_mul g g' hg' _ _ (hu' 0) hrest O hO f, ih (fun i => u i.succ) (fun a => hu _) O hO f]

end GlobalTheory.EpsAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsolutelyIntegrallyClose
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.HInvAic

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]

theorem eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]
  exact (hf n).comp (hg n)

theorem eqv_spMap_equiv {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (F : Shv R) :
    Eqv R (spMap (e : A →+* B)) F := by
  intro n
  have h1 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _ := by
    rw [← spMap_comp]; convert spMap_id B; ext x; simp
  have h2 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _ := by
    rw [← spMap_comp]; convert spMap_id A; ext x; simp
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h2, pull_id]
  · rw [← pull_comp, h1, pull_id]

end GlobalTheory.HInvAic

namespace GlobalTheory.HInvAic

theorem alg (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O] :
    AIC T → SH O → IndEt T O → IsDomain O ∧ AIC O := by
  intro hT hSH hInd
  obtain ⟨hH, -⟩ := hSH
  obtain ⟨-, hac⟩ := (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT
  haveI : IsIntegrallyClosed T := ((GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT).1
  refine GlobalTheory.T.isDomain_monicRoots_of_isIndEtale_local T O hInd ?_
  intro E _ _ _ P _
  obtain ⟨hd, hc⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale T P (Localization.AtPrime P)
  exact ⟨hd, (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed _).2 ⟨hc, GlobalTheory.T.isAlgClosed_fractionRing_atPrime_of_etale' T E P hac⟩⟩
end GlobalTheory.HInvAic

namespace GlobalTheory.HInvAic

theorem tensor_map_eq (T O : Type) [CommRing T] [CommRing O] [Algebra T O] :
    (Algebra.TensorProduct.map (AlgHom.id T O) (Algebra.ofId T (Polynomial T))).toRingHom =
      (((polyEquivTensor T O).toRingEquiv : Polynomial O →+* O ⊗[T] Polynomial T).comp Polynomial.C).comp
        ((Algebra.TensorProduct.rid T T O).toRingEquiv : O ⊗[T] T →+* O) := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o t =>
    simp only [RingHom.comp_apply, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
      Algebra.TensorProduct.rid_tmul, polyEquivTensor_apply, Polynomial.eval₂_C]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.ofId_apply, Polynomial.algebraMap_eq]
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one, Polynomial.algebraMap_eq]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem main : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T], AIC T → IsUnit (q : T) → HInv q T := by
  intro q _ T _ _ hT hq i
  have hφ : ((Algebra.ofId T (Polynomial T)).toRingHom : T →+* Polynomial T) = Polynomial.C := by
    ext x <;> simp [Algebra.ofId_apply]
  rw [← hφ]
  refine GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) T T (Polynomial T) (Algebra.ofId T (Polynomial T)) ?_
  intro O _ _ hSH hInd
  obtain ⟨hdom, haic⟩ := alg T O hT hSH hInd
  obtain ⟨hH, -⟩ := hSH
  have hqO : IsUnit (q : O) := by simpa using hq.map (algebraMap T O)
  have hC := GlobalTheory.T.etaleHomotopyInvariance_absIntClosedLocalDomain q O haic hqO i
  rw [tensor_map_eq, spMap_comp, spMap_comp]
  exact eqv_comp _ _ _ (eqv_comp _ _ _ (eqv_spMap_equiv _ _) hC) (eqv_spMap_equiv _ _)

end GlobalTheory.HInvAic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverByPolarizationPowerSectionsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_cover_by_polarization_power_sections : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∃ (k : ℕ) (I : Type) (s : I → SecM (𝟙 P₀.A.left) P₀.L k), 1 ≤ k ∧ ⨆ i, Out.nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧ ((Out.nonzeroLocus (s i) : P₀.A.left.Opens) : Set P₀.A.left).Nonempty := by
  first | exact @GlobalTheory.AmpleCover.exists_affine_cover_secM | exact GlobalTheory.AmpleCover.exists_affine_cover_secM | (intros; apply GlobalTheory.AmpleCover.exists_affine_cover_secM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenInteriorContainingToricChartGenerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_interior_containing_toricChart_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U W : Y.X.affineOpens), W.1 = U.1 ⊓ interior Y → ∀ (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∃ h : Γ(Y.X, U.1), Y.X.basicOpen h ≤ W.1 ∧ GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 := by
  first | exact @GlobalTheory.LocReg.exists_basicOpen_chartHom_ne_zero | exact GlobalTheory.LocReg.exists_basicOpen_chartHom_ne_zero | (intros; apply GlobalTheory.LocReg.exists_basicOpen_chartHom_ne_zero <;> assumption)
end

