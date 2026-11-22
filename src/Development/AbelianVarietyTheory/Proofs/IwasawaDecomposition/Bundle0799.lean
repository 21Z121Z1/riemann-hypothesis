import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0717
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0904
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSumLeOfLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0960
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0971
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0836
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0962
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0784
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0764
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0753
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0685
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0782
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0748
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0997
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0998
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0982
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0705
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0765
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0777
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0766
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0781
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0786
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricLawsAllStates
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

theorem GlobalTheory.HeightCounting.Up.geometric_laws_of_lb1 : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ P x => ∀ (l : SeriesLevel hL x) (i : (Dof x).ntw.Tw), GlobalTheory.GeoTie.GeoLaws l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) := by
  intro hP hS hL
  have hH := GlobalTheory.T.hecke_geometric_all_states hP hS hL
  refine hH.trans (StepW.of_all fun K B f T w _ _ hw P x l i => ?_)
  have hint := (Dof x).nth.iC_int i
  refine ⟨?_, ?_, ?_, hw P x l i, ?_, ?_, ?_⟩
  · intro b j
    exact GlobalTheory.PointsDetectAlg.detects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hint b j
  · intro b j
    exact GlobalTheory.GeoTie.supDescent_side _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hint b j
  · intro b j f
    exact l.b.ser.sup i _ b _ _ f
  · intro b j
    exact GlobalTheory.T.heckeQuotient_integral_framed_point_complete_field hS.hkInt _ _ _ _ _ _ _ _ _ _ _ x.m.z.geo.κ x.m.z.geo.v₀ x.m.z.geo.fw _ _ hint b j
  · intro j k Pl hk
    obtain ⟨hHP, -⟩ := GlobalTheory.T.isSplitHeckePrimeOffLevel_of_heckeIndexPlace _ _ x.m.z.geo.fw.laws i k Pl hk
    obtain ⟨n, hn⟩ := GlobalTheory.HeckeCount.card_hkKer_const _ _ _ _ (x.m.z.core.Q.Xo ((j : ℕ) + 1)) x.m.z.core.Q.c Pl.asIdeal
      (GlobalTheory.GeoTie.charAt Pl) k (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 hHP)
    exact ⟨n, fun b z => hn _ z.1⟩
  · intro j hj b
    exact l.b.ser.off i j b (fun h => hj (Finset.mem_Icc.2 h))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralEqZeroOfMemRelIdealStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmannProductIntegral_eq_zero_of_mem_relIdeal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Q ∈ relIdeal H Dw → intGr H Dw Q = 0 := by
  first | exact @GlobalTheory.GrassTop.intGr_eq_zero_of_mem_relIdeal | exact GlobalTheory.GrassTop.intGr_eq_zero_of_mem_relIdeal | (intros; apply GlobalTheory.GrassTop.intGr_eq_zero_of_mem_relIdeal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralPointClassEqOne
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

noncomputable section

namespace GlobalTheory.GrassTop

theorem intGr_pointPoly : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H),
    intGr H Dw (pointPoly H Dw) = 1 := by
  intro E _ _ _ H Dw
  unfold intGr
  rw [← GlobalTheory.GoodMetric.antisymm_chernRoots_mul_fibrePoint, degFl_rho_antisymm, prod_factorial_mult,
    rho_eq_flagMap, ← GlobalTheory.Schubert.schubGam_apply, GlobalTheory.SchubertPoint.schubGam_pointPoly, mul_one]
  have hne : ((Dw.p.factorial * Dw.q.factorial : ℝ) ^ Fintype.card (GlobalTheory.AllWt.Psi H)) ≠ 0 := by
    apply pow_ne_zero
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _) (by exact_mod_cast Nat.factorial_ne_zero _)
  exact div_self hne

end GlobalTheory.GrassTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPolyhedralCoverBalancedFormsCMField
section
noncomputable section

open Matrix NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

section Cover

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

theorem hasRedCover_of_fintype (bar : O → O) {ι : Type} [Fintype ι] (f : ι → LinearMap.BilinForm ℤ X)
    (h1 : ∀ i y z, f i y z = f i z y) (h2 : ∀ i y, 0 ≤ f i y y)
    (h : ∀ B ∈ psdCone bar X, ∃ (e : X ≃ₗ[O] X) (c : ι → ℝ), (∀ i, 0 ≤ c i) ∧
      pullR e.toLinearMap B = ∑ i, c i • toReal (f i)) : HasRedCover bar X := by
  let q := Fintype.equivFin ι
  refine ⟨1, fun _ => Fintype.card ι, fun _ i => f (q.symm i), fun _ i => h1 _, fun _ i => h2 _, fun B hB => ?_⟩
  obtain ⟨e, c, hc, he⟩ := h B hB
  refine ⟨e, 0, fun i => c (q.symm i), fun i => hc _, ?_⟩
  rw [he]
  exact (q.symm.sum_comp fun i => c i • toReal (f i)).symm

def sqForm {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (l : Fin n → ℤ) : LinearMap.BilinForm ℤ X :=
  let φ : X →ₗ[ℤ] ℤ := ∑ i, l i • b.coord i
  (LinearMap.mul ℤ ℤ).compl₁₂ φ φ

theorem sqForm_apply {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (l : Fin n → ℤ) (y z : X) :
    sqForm b l y z = (∑ i, l i * b.repr y i) * ∑ i, l i * b.repr z i := by
  simp [sqForm, LinearMap.sum_apply]
  rw [Finset.sum_mul_sum, Finset.sum_comm]

theorem sqForm_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (l : Fin n → ℤ) (i j : Fin n) :
    sqForm b l (b i) (b j) = l i * l j := by
  simp [sqForm_apply, Finsupp.single_apply]

theorem exists_equiv_of_actMat_eq {n : ℕ} (b b' : Module.Basis (Fin n) ℤ X)
    (h : (actMat b : O →+* _) = actMat b') : ∃ e : X ≃ₗ[O] X, ∀ i, e (b i) = b' i := by
  let g : X ≃ₗ[ℤ] X := b.equiv b' (Equiv.refl _)
  have hg : ∀ i, g (b i) = b' i := fun i => by simp [g]
  have key : ∀ (c : O) (x : X), g (c • x) = c • g x := by
    intro c x
    have h1 : (g.toLinearMap ∘ₗ (Module.toModuleEnd ℤ X c)) = (Module.toModuleEnd ℤ X c) ∘ₗ g.toLinearMap := by
      refine b.ext fun j => ?_
      change g (c • b j) = c • g (b j)
      rw [hg]
      calc g (c • b j) = g (∑ i, b.repr (c • b j) i • b i) := by rw [b.sum_repr]
        _ = ∑ i, b.repr (c • b j) i • b' i := by simp only [map_sum, map_smul, hg]
        _ = ∑ i, b'.repr (c • b' j) i • b' i := Finset.sum_congr rfl fun i _ => by
            have := congrFun (congrFun (congrArg (fun ρ : O →+* Matrix (Fin n) (Fin n) ℤ => ρ c) h) i) j
            simp only [actMat_apply] at this
            rw [this]
        _ = c • b' j := b'.sum_repr _
    exact LinearMap.congr_fun h1 x
  exact ⟨(g.toAddEquiv).toLinearEquiv key, hg⟩

theorem actMat_balanced {bar : O → O} {n : ℕ} (b : Module.Basis (Fin n) ℤ X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ}
    (hB : B ∈ realForms bar X) {G : Matrix (Fin n) (Fin n) ℝ} (hG : ∀ i j, B (b i) (b j) = G i j) (c : O) :
    ((actMat b c).map (Int.cast : ℤ → ℝ))ᵀ * G = G * (actMat b (bar c)).map (Int.cast : ℤ → ℝ) := by
  ext i j
  have e1 : B (c • b i) (b j) = ∑ k, (b.repr (c • b i) k : ℝ) * G k j :=
    calc B (c • b i) (b j) = B (∑ k, b.repr (c • b i) k • b k) (b j) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hG, zsmul_eq_mul]
  have e2 : B (b i) (bar c • b j) = ∑ k, G i k * (b.repr (bar c • b j) k : ℝ) :=
    calc B (b i) (bar c • b j) = B (b i) (∑ k, b.repr (bar c • b j) k • b k) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, hG, zsmul_eq_mul, mul_comm]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, actMat_apply]
  rw [← e1, ← e2]
  exact hB.2 c _ _

end Cover

theorem hasRedCover (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] : HasRedCover H.bar X := by
  classical
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  haveI : Module.Projective ℤ X := by
    obtain ⟨i, hi⟩ := Module.projective_def'.1 (inferInstance : Module.Projective (𝓞 E) X)
    exact Module.Projective.of_split (i.restrictScalars ℤ) ((Finsupp.linearCombination (𝓞 E) id).restrictScalars ℤ)
      (LinearMap.ext fun x => LinearMap.congr_fun hi x)
  haveI : Module.Free ℤ X := inferInstance
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℤ X = n := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀, hB₀'⟩ := GlobalTheory.T.exists_posDef_balanced_realForm_cmField E H X
  have hF := GlobalTheory.T.finite_balanced_cmIntegers_actions_siegelReduced E H n
  obtain ⟨S, hS⟩ := GlobalTheory.T.siegelGram_mem_cone_integer_squares n
  haveI : Nonempty (Module.Basis (Fin n) ℤ X) := ⟨Module.finBasisOfFinrankEq ℤ X hn⟩
  let ref : (𝓞 E →+* Matrix (Fin n) (Fin n) ℤ) → Module.Basis (Fin n) ℤ X := fun ρ => Classical.epsilon fun b => actMat b = ρ
  let ι := ↥hF.toFinset × ↥S
  refine hasRedCover_of_fintype (ι := ι) _ (fun x => sqForm (ref x.1.1) x.2.1) (fun x y z => ?_) (fun x y => ?_) fun B hB => ?_
  · simp only [sqForm_apply, mul_comm]
  · simp only [sqForm_apply]; exact mul_self_nonneg _
  obtain ⟨b, d, d', u, B', h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_adapted_siegel_basis_balanced_forms E H X B₀ hB₀ hB₀' n hn B hB
  have hρ : (actMat b : 𝓞 E →+* _) ∈ hF.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨d', u, h2, h3, fun c => actMat_balanced b h4 h6 c⟩
  set ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ := actMat b with hρdef
  have href : actMat (ref ρ) = ρ := Classical.epsilon_spec (p := fun b => actMat b = ρ) ⟨b, rfl⟩
  obtain ⟨e, he⟩ := exists_equiv_of_actMat_eq (O := 𝓞 E) (ref ρ) b href
  obtain ⟨c, hc, hG⟩ := hS d u h1
  refine ⟨e, fun x => if x.1.1 = ρ then c x.2.1 else 0, fun x => ?_, ?_⟩
  · dsimp only; split_ifs
    · exact hc _
    · exact le_rfl
  refine (ref ρ).ext fun i => (ref ρ).ext fun j => ?_
  have hl : B (b i) (b j) = ∑ l ∈ S, c l * ((l i : ℝ) * (l j : ℝ)) := by
    rw [h5, hG]
    simp [Matrix.sum_apply, vecMulVec_apply]
  simp only [pullR_apply, LinearEquiv.coe_coe, he, hl, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (⟨ρ, hρ⟩ : ↥hF.toFinset)]
  · simp only [if_true, sqForm_basis]
    rw [← Finset.sum_coe_sort S]
    push_cast
    rfl
  · intro y _ hy
    have : y.1 ≠ ρ := fun h => hy (Subtype.ext h)
    simp [this]
  · simp

end GlobalTheory.RedTh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqRationalDataOfEigen
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple.Lay.EigCopy

set_option maxHeartbeats 4000000 in

theorem parIn_built {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : NTrue hL D' cf' C' tp') (rep' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r)
    (hrep : HEq nt.rep rep') :
    ∃ Rw : RowSide D', HEq Rw.locR nt.A.row.locR ∧ Nonempty (ParIn hL D' cf' rep' Rw) := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have hr : rep = rep' := eq_of_heq hrep
  subst hr
  let T : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { A.wdT with }
  let Rw : RowSide (withLoc L) := { A.row with }
  exact ⟨Rw, HEq.rfl, ⟨{ T := T, lab := A.lab, chr := { A.chr with }, cg := { cg with }, A := { A.au with }, au := au, row := row }⟩⟩

theorem eigTrue_congr {D : D7} {cf : CharFrame D} {Rw Rw' : RowSide D} {Sb : Finset (PlE D.host)}
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} (h : Rw.locR = Rw'.locR) (hT : GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig) :
    GlobalTheory.TwInputs.EigTrue D cf Rw' Sb eig := by
  unfold GlobalTheory.TwInputs.EigTrue at hT ⊢
  rw [← h]
  exact hT

set_option maxHeartbeats 4000000 in

theorem eig_atMem : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ _ _ c => ∀ (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ), HEq S (ratL c.a.nt.L c.a.nt.S) → HEq hL' c.a.nt.hL → HEq eig c.a.nt.eig → HEq θ c.a.nt.θ → ∃ Sb : Finset (PlE (w.D Z).host), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (w.D Z) (TC.cf w.I w.l Z) Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig := by
  intro hN hS hL
  refine GlobalTheory.GalLoc.atMem_imp (GlobalTheory.GalLoc.atMem_and (GlobalTheory.T.exists_enlarged_hecke_set hN hS hL) (GlobalTheory.T.level_character_of_local_langlands hN hS hL)) ?_
  intro K B f T w Z Wt p0 t nch n xd c hE H S hL' eig θ hS' hhL heig hθ
  obtain ⟨H2, H3⟩ := H
  obtain ⟨e⟩ := hE
  have e' : NMore (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  obtain ⟨Sb, eg, hSb, heq, hAd⟩ := e'.eig
  obtain ⟨Sb', hsub, hS0, hlow, hrd⟩ := H2 Sb hSb
  obtain ⟨θ0, hθ0, hψ⟩ := H3
  obtain ⟨Rw0, hRw0, ⟨hpar⟩⟩ := parIn_built c.a.nt _ c.row.rep_eq
  have hT := GlobalTheory.TwInputs.Eig.eigTrue hL t.r.Y t.r.z.pins.char.base.lev hpar.T Rw0 hpar.row hAd hsub hlow
  have hO := GlobalTheory.TwInputs.Eig.eigOcc t.r.Y t.r.z.pins.char.base.lev t.r.intersectionNumber_baseChange.prim.unif t.r.z.pins.char.base.models.HW
    t.r.z.good.2 hψ hAd hsub hlow hrd
  rw [t.r.z.lev.C] at hT
  obtain rfl : S = _ := eq_of_heq (hS'.trans c.row.S_eq)
  obtain rfl : hL' = c.row.hecke.hL := eq_of_heq (hhL.trans c.row.hL_eq)
  obtain rfl : eig = eg := eq_of_heq (heig.trans heq)
  obtain rfl : θ = θ0 := eq_of_heq (hθ.trans hθ0.symm)
  refine ⟨Sb', hS0, fun Rw hRw => ⟨eigTrue_congr ?_ hT, hO⟩⟩
  exact eq_of_heq (hRw0.trans hRw.symm)

end GlobalTheory.RowTriple.Lay.EigCopy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieFramesSmoothHermitianOffBoundary
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.FlagBundle GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.ProjVar

namespace GlobalTheory.LieBase

open scoped ComplexOrder
open Matrix GlobalTheory GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.GoodMetric GlobalTheory.ProjVar.Var GlobalTheory.TrueGeo.Res

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {σ : c.F →+* ℂ} {e : F ≃+* c.F} {X : Var F} {j : X.X ⟶ gen Z}
  {f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)} {S : Fr (ratOf X) Dw.mult 0} {A₀ : Mat Dw.mult X.Fn}

theorem spMap_evStalk_eq (y : CxPts X.str (σ.comp e.toRingHom)) : y.1 = spMap (evStalk y) ≫ stalkPt X (under y) :=
  (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1).symm

theorem exists_frameAt (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (hT : Tied e X j f₀ S A₀)
    (y : CxPts X.str (σ.comp e.toRingHom)) {A : Mat Dw.mult X.Fn} (hA : A ∈ S.S (under y)) :
    ∃ g : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z), FrameAt e f₀ A₀ A y g := by
  obtain ⟨φ, fz, hc⟩ := hT.2 (under y) A hA
  have hφ : σ = (evStalk y).comp φ := RingHom.ext fun a => by
    have h3 : φ a = algebraMap F _ (e.symm a) := IsFractionRing.injective _ X.X.functionField
      ((RingHom.congr_fun hc.2.1 a).symm.trans ((X.stalkIncl (under y)).commutes _).symm)
    show σ a = evStalk y (φ a)
    rw [h3]
    refine Eq.trans ?_ ((evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top _)).symm
    simp
  have hx : (cxOf e σ hj y).1 ≫ genι Z = spMap (evStalk y) ≫ stalkPt X (under y) ≫ j ≫ genι Z := by
    show (y.1 ≫ j) ≫ genι Z = _
    rw [spMap_evStalk_eq y]
    exact Category.assoc _ _ _
  obtain ⟨g, hg⟩ := fz.exists_isMap (evStalk y) hφ hx
  exact ⟨g, φ, fz, evStalk y, spMap_evStalk_eq y, hc, hg⟩

theorem map_ratVal_eq_co (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (hT : Tied e X j f₀ S A₀)
    {y : CxPts X.str (σ.comp e.toRingHom)} {A A' : Mat Dw.mult X.Fn} (hA' : A' ∈ S.S (under y)) {g g' : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z)} (hg : FrameAt e f₀ A₀ A y g)
    (hg' : FrameAt e f₀ A₀ A' y g') (τ : E →+* ℂ) : (A' * A⁻¹).map (ratVal · y) τ = (g.co g' τ)ᵀ := by
  obtain ⟨φ, fz, ψ, hψ, hc, hm⟩ := hg
  obtain ⟨φ', fz', ψ', hψ', hc', hm'⟩ := hg'
  obtain rfl : ψ = evStalk y :=
    EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under y))).1 (hψ.symm.trans (spMap_evStalk_eq y)))
  obtain rfl : ψ' = evStalk y :=
    EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under y))).1 (hψ'.symm.trans (spMap_evStalk_eq y)))
  obtain rfl : φ' = φ := RingHom.ext fun a => IsFractionRing.injective _ X.X.functionField
    ((RingHom.congr_fun hc'.2.1 a).symm.trans (RingHom.congr_fun hc.2.1 a))
  have hx : (cxOf e σ hj y).1 ≫ genι Z = spMap (evStalk y) ≫ stalkPt X (under y) ≫ j ≫ genι Z := by
    show (y.1 ≫ j) ≫ genι Z = _
    rw [spMap_evStalk_eq y]
    exact Category.assoc _ _ _
  obtain ⟨k, hk⟩ := fz.exists_isMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) hc.2.1 hc.1
  obtain ⟨k', hk'⟩ := fz'.exists_isMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) hc.2.1 hc.1
  have h1 : k.co f₀ τ = ((A₀ * A⁻¹) τ)ᵀ := EigFrame.co_eq fun i => by rw [funext (hk τ)]; exact hc.2.2 τ i
  have h2 : k'.co f₀ τ = ((A₀ * A'⁻¹) τ)ᵀ := EigFrame.co_eq fun i => by rw [funext (hk' τ)]; exact hc'.2.2 τ i
  have h3 : k.co k' τ = (fz.co fz' τ).map (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) :=
    hk.co τ hk' hc.1
  have h4 := k.co_mul k' f₀ τ
  rw [h1, h2, h3] at h4
  set M := (fz.co fz' τ).map (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) with hM
  have u0 : IsUnit (A₀ τ).det := isUnit_iff_ne_zero.2 (Fr.det_ne hT.1 τ)
  have u' : IsUnit (A' τ).det := isUnit_iff_ne_zero.2 (Fr.det_ne hA' τ)
  have h5 : A' τ * (A τ)⁻¹ = Mᵀ := by
    have h6 := congrArg Matrix.transpose h4
    rw [transpose_mul, transpose_transpose, transpose_transpose] at h6
    change A₀ τ * (A' τ)⁻¹ * Mᵀ = A₀ τ * (A τ)⁻¹ at h6
    have h7 : A' τ * (A₀ τ)⁻¹ * (A₀ τ * (A' τ)⁻¹) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A₀ τ)⁻¹, Matrix.nonsing_inv_mul _ u0, Matrix.one_mul,
        Matrix.mul_nonsing_inv _ u']
    calc A' τ * (A τ)⁻¹ = A' τ * (A₀ τ)⁻¹ * (A₀ τ * (A τ)⁻¹) := by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A₀ τ)⁻¹, Matrix.nonsing_inv_mul _ u0, Matrix.one_mul]
      _ = Mᵀ := by rw [← h6, ← Matrix.mul_assoc, h7, Matrix.one_mul]
  rw [hm.co τ hm' hx]
  change ((A' τ * (A τ)⁻¹)).map (ratVal · y) = _
  rw [h5]
  ext a b
  simp only [map_apply, transpose_apply, hM]
  rw [ratVal_eq_valAt y ⟨_, rfl⟩, valAt_algebraMap]
  rfl

theorem isMetricOn_gramOf (G : EigMet Z σ) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (hT : Tied e X j f₀ S A₀)
    (Ω : X.X.Opens) (hs : ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) Ω, ∀ A ∈ S.S (under y), ∀ (τ : E →+* ℂ)
      (a b : Fin (Dw.mult τ)), CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).re) y ∧
        CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).im) y) :
    IsMetricOn S Ω (gramOf e G hj f₀ A₀) := by
  refine ⟨fun y _ A hA τ => ?_, fun y hy A hA τ a b => hs y hy A hA τ a b, fun y _ A hA A' hA' τ => ?_⟩
  · have h := exists_frameAt hj hT y hA
    rw [gramOf, dif_pos h]
    exact (G.pos _ _ τ).transpose
  · have h := exists_frameAt hj hT y hA
    have h' := exists_frameAt hj hT y hA'
    unfold gramOf
    rw [dif_pos h, dif_pos h']
    rw [G.change _ h.choose h'.choose τ, map_ratVal_eq_co hj hT hA' h.choose_spec h'.choose_spec τ]
    rw [transpose_mul, transpose_mul, Matrix.mul_assoc]
    congr 2

end GlobalTheory.LieBase

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier

theorem GlobalTheory.LieBase.isMetricOn_lieGram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsMetricOn Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU C X j f f₀ Eb A₀ hj hL
  have := T.smooth
  obtain ⟨hoi, -, hT⟩ := hL
  rw [lieGram_eq_gramOf]
  exact isMetricOn_gramOf (hodgeMet T.Z U) hj hT _
    (GlobalTheory.T.eigenMetricGram_smooth_in_familyFrames E H Dw l Xo c O β T.Z σ _ (GlobalTheory.T.hodgeMetric_uniformisation_smoothOn_interior E H Dw l Xo c O β T.Z σ U hσ hU) F e X j f₀ Eb A₀ hj hoi hT)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyFanOfStarSubdivisionCellsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPolyFan_of_starSubdivision_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → IsStarOf H.bar q ψ w ψ' → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, ψ'.evalZ β = n) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ψ'.evalZ β) → IsPolyFan H.bar q ψ' := by
  first | exact @GlobalTheory.PolFan.StarFan.isPolyFan_star | exact GlobalTheory.PolFan.StarFan.isPolyFan_star | (intros; apply GlobalTheory.PolFan.StarFan.isPolyFan_star <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFinEMemDivisorStandard
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.FrameInt

theorem exists_split (D : D7) (PP : HeightOneSpectrum (𝓞 D.host.E)) (h : ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP) :
    ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = PP := by
  refine GlobalTheory.RowUnitProof.exists_splitPlace_eq D PP ?_
  by_contra hs
  refine h fun c hc => ?_
  by_contra hn
  exact hs ⟨c, hc, fun y hy hm => hn ⟨y, hm, hy.trans (GlobalTheory.TypePlaces.star_eq_conj D _).symm⟩⟩

theorem frame_of {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0)
    (hF : D.host.F = maximalRealSubfield D.host.E) (k : Fin D.R.m) (P : principalLevelFrame.RowPsi (Vc D k) D.R.nV)
    (hP : R3.StdFrame hF P) (s : T) :
    (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, Formalism.IndefR.Lev.finE (Vc D k) (P.ψ κ) ∈ Formalism.L2.DIV.St (L.βV k)) ∧
    ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) P (L.βV k) s' φ b := by
  have hβ : IsBaseFrame (Vc D k) (L.βV k) (L.ΛV k) 1 := by
    obtain ⟨c, hc⟩ := hL.βV k
    rwa [one_pow] at hc
  refine ⟨fun κ hκ => ?_, fun PP h => ?_⟩
  · have h1 := (hP.2 κ).1 hκ
    exact (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ h1.1).2 h1
  · have hn : ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP :=
      h.elim (fun h => GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg hL.Pg PP h PP h) fun h => (hL.Q_pl s PP h).2 PP h
    obtain ⟨s', hs'⟩ := exists_split D PP hn
    obtain ⟨φ, b, h1, h2⟩ := GlobalTheory.T.exists_split_reduction_standard_frame_conj D (Vc D k) D.R.nV (GlobalTheory.FrameBlockDiagonal.rankV D k) hF P (L.βV k) (L.ΛV k) hP hβ s'
    exact ⟨s', φ, b, hs', h1, h2⟩

theorem main : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (k : Fin (w.st Z).toD7.R.m) s,
    (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
      Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc (w.st Z).toD7 k) ((ad.PV k).ψ κ) ∈ Formalism.L2.DIV.St (t.r.z.R.βV k)) ∧
    ∀ PP, PP ∈ t.r.z.R.Pg ∨ PP ∈ t.r.z.R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b :=
  fun hL => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ ad k s =>
    frame_of (D := (w.st Z).toD7) t.r.z.R.toLevCh t.r.z.pins.char.base.lev t.r.Y.hF k (ad.PV k) (ad.std k) s

end GlobalTheory.FrameInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedConstructionStatesCharactersAgreeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linked_construction_states_characters_agree : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Chars (sideAt x g hg a) (sideAt x' g' hg' a') := by
  first | exact @GlobalTheory.HeightCounting.SerMove.chars_of_link | exact GlobalTheory.HeightCounting.SerMove.chars_of_link | (intros; apply GlobalTheory.HeightCounting.SerMove.chars_of_link <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCoefficientFieldFiniteGroupEqStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedStates_coefficientField_finiteGroup_eq : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∃ (eK : ↥(sideAt x g hg a).core.Q.c.F ≃+* ↥(sideAt x' g' hg' a').core.Q.c.F) (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ y, ((eK y : ↥(sideAt x' g' hg' a').core.Q.c.F) : ℂ) = (y : ℂ)) ∧ ∀ u, HEq (γ u) u := by
  first | exact @GlobalTheory.HeightCounting.SerMove.Ids.field_group_of_link | exact GlobalTheory.HeightCounting.SerMove.Ids.field_group_of_link | (intros; apply GlobalTheory.HeightCounting.SerMove.Ids.field_group_of_link <;> assumption)
end

