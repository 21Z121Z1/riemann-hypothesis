import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0313
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0310
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0294
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0288
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0002
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTwistPrimeInvariantCongruentFrames
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
import Formalism.SharpRestriction.GlobalSchurBounds.Joints

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldUniformizerAtSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.RealUnifSplit

theorem le_exp_neg_one_of_lt {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, neg_add_cancel,
    WithZero.exp_zero]
  exact h

theorem val_sq_le {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (z : 𝓞 L) (hz : z ∈ s.w.asIdeal ^ 2) :
    Valued.v (s.i (z : L)) ≤ WithZero.exp (-2) := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro a ha b hb
    have ha' : Valued.v (s.i (a : L)) < 1 := (s.split_mem_ideal a).1 ha
    have hb' : Valued.v (s.i (b : L)) < 1 := (s.split_mem_ideal b).1 hb
    show Valued.v (s.i ((a : L) * (b : L))) ≤ _
    rw [map_mul, map_mul]
    calc Valued.v (s.i (a : L)) * Valued.v (s.i (b : L))
        ≤ WithZero.exp (-1) * WithZero.exp (-1) :=
          mul_le_mul' (le_exp_neg_one_of_lt ha') (le_exp_neg_one_of_lt hb')
      _ = WithZero.exp (-2) := by rw [← WithZero.exp_add]; norm_num
  · intro a b ha hb
    show Valued.v (s.i ((a : L) + (b : L))) ≤ _
    rw [map_add]
    exact le_trans (Valuation.map_add _ _ _) (max_le ha hb)

end GlobalTheory.RealUnifSplit

theorem GlobalTheory.realUnif_split {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    ∃ y : 𝓞 L, y ∈ s.w.asIdeal ∧ y ∉ s.w.asIdeal ^ 2 ∧ Formalism.AUTREP.IsUnif L s.v (s.i (y : L)) := by
  obtain ⟨π, hπ⟩ := s.v.intValuation_exists_uniformizer
  have hv : Valued.v (s.i ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) π : 𝓞 L) : L)) =
      WithZero.exp (-1) := by
    rw [s.split_val_alg, HeightOneSpectrum.valuation_of_algebraMap, hπ]
  refine ⟨algebraMap _ (𝓞 L) π, ?_, ?_, hv⟩
  · refine (s.split_mem_ideal _).2 ?_
    rw [hv]; rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · intro h
    have h2 := GlobalTheory.RealUnifSplit.val_sq_le s _ h
    rw [hv] at h2
    have := WithZero.exp_le_exp.1 h2
    omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFramesStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vector_prescribed_cosets_badPrimes_frames : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (f : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n)) (y0 : rowSG Pr sel mu → Sp X.E n),
  ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((f P).symm y) (y0 P) := by
  first | exact @GlobalTheory.CosetApprox.exists_sameCoset | exact GlobalTheory.CosetApprox.exists_sameCoset | (intros; apply GlobalTheory.CosetApprox.exists_sameCoset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtAdeleMulOfPlaceComponentEqZeroStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intAtAdele_mul_of_placeComponent_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v Q → ∀ a : TensorProduct F E (FiniteAdeleRing (𝓞 F) F), Formalism.UG.prV (E := E) v a = 0 → ∀ c : E, Formalism.L2.Col.IntAtA (F := F) Q (Formalism.L2.Col.iA F E c * a) := by
  first | exact @GlobalTheory.VanishAtOver.intAtA_mul_of_prV_eq_zero | exact GlobalTheory.VanishAtOver.intAtA_mul_of_prV_eq_zero | (intros; apply GlobalTheory.VanishAtOver.intAtA_mul_of_prV_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicLocalComponentFixedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypic_local_component_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] σ.V, φ f ≠ 0 ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f' ∈ NG.isoTyp a.ρ S, φ (NG.rt L n x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) (φ f') := by
  first | exact @GlobalTheory.SepLoc.main | exact GlobalTheory.SepLoc.main | (intros; apply GlobalTheory.SepLoc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumConditionsAtStandardKernelComparison
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.PdvTie

theorem at_of_stdTie : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (O : Obj D) (t : KerEntTied O.ex), StdTie D O t → 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 → (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) → GlobalTheory.Pdv.At O.ex t.ent := by
  intro hA hG hC hI D O t hT hs h1 h2 hE
  refine StdTie.ind (R := fun D O t => 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 →
      (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) →
      GlobalTheory.Pdv.At O.ex t.ent) ?_ hT hs h1 h2 hE
  intro B X I l l0 Z O t h hs h1 h2 hE
  exact GlobalTheory.PdvClose.at_of_true_columns hA hG hC hI I h.ok h.pins l Z l0 O.L O.gatT O.Gx O.Gy O.K O.X O.cX O.ex t
    (GlobalTheory.Pdv.colNorm_of_tw I h.isTw) h.jets h.tw h.ker h.entC h.adapted h.top hs h1 h2 hE

end GlobalTheory.PdvTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumEquivariantRationalUnitary
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TopRat

section Frames
variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) {u : Pr.Word} {j : ℕ}

theorem frsF_rat_notG (p : ChPt (R := R) sel mu u j) (g : UF X.E (R.N j)) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) :
    frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
      g.1 * frsF sel mu p P := by
  unfold frsF
  rw [dif_neg hP, dif_neg hP]
  show g.1 * p.fr _ * (((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 = _
  simp

theorem frsF_rat_G (hq : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (p : ChPt (R := R) sel mu u j) (g : UF X.E (R.N j)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    ∃ κ : ↥(GLint X.E (R.N j) P.1),
      frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
        g.1 * frsF sel mu p P * κ.1 ∧
      ∀ x ∈ stdAt X.E (R.N j) P.1, ((qOf P.1 : X.E) ^ 1)⁻¹ • (κ.1 x - x) ∈ stdAt X.E (R.N j) P.1 := by
  obtain ⟨κ, he, hr⟩ := liftFr_smul p.deco (g, (1 : GLG X.E (R.N j) Pr.vGs)) ⟨P.1, hP⟩
  refine ⟨κ, ?_, fun x hx => ?_⟩
  · unfold frsF
    rw [dif_pos hP, dif_pos hP]
    exact he
  · rw [GlobalTheory.TopStep.mem_stdAt]
    intro i
    have hkx := GlobalTheory.TopStep.mem_stdAt.1 ((κ.2 x).2 hx) i
    have hxi := GlobalTheory.TopStep.mem_stdAt.1 hx i
    have h1 := congrFun (hr x hx) i
    simp only [Pi.one_apply, inv_one, Units.val_one, Matrix.one_mulVec] at h1
    have hred : redP P.1 (κ.1 x i - x i) = 0 := by
      rw [GlobalTheory.TopStep.reduction_sub hkx hxi]
      have h2 : redP P.1 (κ.1 x i) = redP P.1 (x i) := h1
      rw [h2, sub_self]
    have h := GlobalTheory.TopStep.intAt_div_of_redP (hq P hP) (GlobalTheory.TopStep.intAt_sub hkx hxi) hred
    have e : (((qOf P.1 : X.E) ^ 1)⁻¹ • (κ.1 x - x)) i = (κ.1 x i - x i) / (qOf P.1 : X.E) := by
      simp [div_eq_inv_mul]
    rw [e]
    exact h

end Frames

theorem xiPt_top_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), t.m2 < i → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG t.X.E (D.R.N (i + 1)) t.Pr.vGs × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie i hi hlt β β' x x' p p' _hp _hp' g g' w
  have hm := m_eq t μ
  obtain rfl : i = t.m2 + 1 := by omega
  have hn1 : ¬ (t.m2 + 1 < t.m2) := by omega
  have hn2 : t.m2 + 1 ≠ t.m2 := by omega
  unfold xiPt
  rw [dif_neg hn1, if_neg hn2, dif_neg hn1, if_neg hn2, XiTop_eq, XiTop_eq]
  congr 1
  · exact phiT_smul t.X.K p.deco p'.deco g 1 g' 1 w
  · have hX : t.X.Ok := hPin.fields.ok
    have hok := t.idx_ok μ
    have hc := hok.cst_ok
    have hrep : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
        repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q := by
      intro q
      obtain ⟨y, hy⟩ := GlobalTheory.CplCosetPt.exists_sameCoset_frames t.sel (t.tup μ) (t.cst μ) (fun P => frsF t.sel (t.tup μ) q P)
        (fun P => y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
      exact Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) ⟨y, hy⟩
    have hy0 := GlobalTheory.T.intAt_scaled_baseCosetRep_of_adTie D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie β
    refine Finset.prod_congr rfl fun P _ => ?_
    have hq0 : (qOf P.1 : t.X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
    have hqI : IntAt P.1 (qOf P.1 : t.X.E) := by simpa using IntAt.coe P.1 ((qOf P.1 : ℕ) : 𝓞 t.X.E)
    have hyy : y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P = A.y0 β P := by
      unfold y0At
      rw [dif_pos rfl]
    by_cases hP : P.1 ∈ t.Pr.vGs
    · have hq2 : ∀ P : rowSG t.Pr t.sel (t.tup μ), P.1 ∈ t.Pr.vGs → ((qOf P.1 : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal ^ 2 :=
        fun P hP => GlobalTheory.TopStep.qOf_notMem_sq hX t.pr_ok hP
      obtain ⟨κ, hF, hκc⟩ := frsF_rat_G t.sel (t.tup μ) hq2 p g P hP
      obtain ⟨κ', hF', hκc'⟩ := frsF_rat_G t.sel (t.tup μ) hq2 p' g' P hP
      have hD1 : (t.cst μ).D P = 1 := hok.depthG P hP
      have hκD : ∀ z ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ.1 z - z) ∈ stdAt t.X.E _ P.1 := by
        rw [hD1]; exact hκc
      have hκD' : ∀ z ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ'.1 z - z) ∈ stdAt t.X.E _ P.1 := by
        rw [hD1]; exact hκc'
      have hy0P : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * A.y0 β P l) := by
        intro l
        have h := hy0 P l
        simpa only [hP, if_true, pow_one] using h
      have key1 : ∀ (F1 : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))) (u1 u0 : Sp t.X.E (D.R.N (t.m2 + 1))),
          F1 = g.1 * frsF t.sel (t.tup μ) p P * κ.1 →
          SameCoset t.sel (t.tup μ) (t.cst μ) P (F1.symm u1) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p P).symm u0) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr F1 (g'.1 * frsF t.sel (t.tup μ) p' P * κ'.1) (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap)) (F1.symm u1) =
            topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w) ((frsF t.sel (t.tup μ) p P).symm u0) := by
        rintro F1 u1 u0 rfl h1 h2
        unfold SameCoset at h1 h2
        simp only [hP, if_true, pow_zero, inv_one, one_mul, hyy] at h1 h2
        have e1 : inFr (g.1 * frsF t.sel (t.tup μ) p P * κ.1) (g'.1 * frsF t.sel (t.tup μ) p' P * κ'.1)
            (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) =
            κ'.1.symm.toLinearMap ∘ₗ inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w ∘ₗ κ.1.toLinearMap := by
          refine LinearMap.ext fun v => ?_
          show κ'.1.symm ((frsF t.sel (t.tup μ) p' P).symm (g'.1.symm (g'.1 (w (g.1.symm (g.1 ((frsF t.sel (t.tup μ) p P) (κ.1 v)))))))) = _
          rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
          rfl
        have e2 : (g.1 * frsF t.sel (t.tup μ) p P * κ.1).symm u1 = κ.1.symm ((frsF t.sel (t.tup μ) p P).symm (g.1.symm u1)) := rfl
        rw [e1, e2]
        rw [e2] at h1
        generalize (frsF t.sel (t.tup μ) p P).symm (g.1.symm u1) = v1 at h1 ⊢
        generalize (frsF t.sel (t.tup μ) p P).symm u0 = v at h2 ⊢
        generalize inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w = Yw
        have hbd : ∀ z : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 ((z - A.y0 β P) l)) →
            ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * z l) := by
          intro z hz l
          have e : (qOf P.1 : t.X.E) * z l = (qOf P.1 : t.X.E) * (z - A.y0 β P) l + (qOf P.1 : t.X.E) * A.y0 β P l := by
            simp only [Pi.sub_apply]; ring
          rw [e]
          exact (hqI.mul (hz l)).add (hy0P l)
        have hw : (qOf P.1 : t.X.E) • κ.1.symm v1 ∈ stdAt t.X.E _ P.1 :=
          GlobalTheory.TopStep.mem_stdAt.2 fun l => by simpa using hbd _ h1 l
        have hw1 : (qOf P.1 : t.X.E) • v1 ∈ stdAt t.X.E _ P.1 := by
          have h := (κ.2 ((qOf P.1 : t.X.E) • κ.1.symm v1)).2 hw
          rwa [map_smul, LinearEquiv.apply_symm_apply] at h
        have hv1 : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * v1 l) := fun l => by
          simpa using GlobalTheory.TopStep.mem_stdAt.1 hw1 l
        rw [GlobalTheory.TwV.AwayTopG.topDat_frames_vGs A dtU a hPin hTie P hP κ.1 κ'.1 κ.2 hκD κ'.2 hκD' Yw v1 hv1]
        have hs := GlobalTheory.TwV.AwayTopG.symm_near κ.2 hκc hw1
        rw [map_smul, ← smul_sub, smul_smul, pow_one, inv_mul_cancel₀ hq0, one_smul] at hs
        have hdiff : v1 - v ∈ stdAt t.X.E _ P.1 := by
          refine GlobalTheory.TopStep.mem_stdAt.2 fun l => ?_
          have e : (v1 - v) l = (κ.1.symm v1 - A.y0 β P) l - (κ.1.symm v1 - v1) l - (v - A.y0 β P) l := by
            simp only [Pi.sub_apply]; ring
          rw [e]
          exact GlobalTheory.TopStep.intAt_sub (GlobalTheory.TopStep.intAt_sub (h1 l) (GlobalTheory.TopStep.mem_stdAt.1 hs l)) (h2 l)
        unfold topDat
        congr 1
        have h := GlobalTheory.TopLaw.ftY_comp_glint t.sel (t.tup μ) (t.cst μ) hc P (hok.depthQ P) (κ := 1)
          (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ Yw) v v1 (fun _ => hbd _ h2)
          (fun h => absurd hP h) (fun _ => hdiff) (fun h => absurd hP h)
        exact h
      rw [hF']
      exact key1 _ _ _ hF (hrep _ P) (hrep _ P)
    · have hy0P : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * A.y0 β P l) := by
        intro l
        have h := hy0 P l
        simpa only [hP, if_false] using h
      have hqM : (qOf P.1 : t.X.E) ^ (t.cst μ).M ≠ 0 := pow_ne_zero _ hq0
      have key2 : ∀ (F1 : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))) (u1 u0 : Sp t.X.E (D.R.N (t.m2 + 1))),
          F1 = g.1 * frsF t.sel (t.tup μ) p P →
          SameCoset t.sel (t.tup μ) (t.cst μ) P (F1.symm u1) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p P).symm u0) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr F1 (g'.1 * frsF t.sel (t.tup μ) p' P) (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap)) (F1.symm u1) =
            topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w) ((frsF t.sel (t.tup μ) p P).symm u0) := by
        rintro F1 u1 u0 rfl h1 h2
        unfold SameCoset at h1 h2
        simp only [hP, if_false, hyy] at h1 h2
        have e1 : inFr (g.1 * frsF t.sel (t.tup μ) p P) (g'.1 * frsF t.sel (t.tup μ) p' P)
            (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w := by
          refine LinearMap.ext fun v => ?_
          show (frsF t.sel (t.tup μ) p' P).symm (g'.1.symm (g'.1 (w (g.1.symm (g.1 ((frsF t.sel (t.tup μ) p P) v)))))) = _
          rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
          rfl
        have e2 : (g.1 * frsF t.sel (t.tup μ) p P).symm u1 = (frsF t.sel (t.tup μ) p P).symm (g.1.symm u1) := rfl
        rw [e1, e2]
        rw [e2] at h1
        generalize (frsF t.sel (t.tup μ) p P).symm (g.1.symm u1) = v1 at h1 ⊢
        generalize (frsF t.sel (t.tup μ) p P).symm u0 = v at h2 ⊢
        generalize inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w = Yw
        have hv : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * v l) := by
          intro l
          have e : (qOf P.1 : t.X.E) ^ (t.cst μ).M * v l = (qOf P.1 : t.X.E) ^ (t.cst μ).M * (qOf P.1 : t.X.E) ^ (t.cst μ).M *
              (((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v - A.y0 β P) l) + (qOf P.1 : t.X.E) ^ (t.cst μ).M * A.y0 β P l := by
            simp only [Pi.sub_apply]
            field_simp
            ring
          rw [e]
          exact (((GlobalTheory.TopStep.intAt_pow hqI _).mul (GlobalTheory.TopStep.intAt_pow hqI _)).mul (h2 l)).add (hy0P l)
        have hdiff : ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • (v1 - v) ∈ stdAt t.X.E _ P.1 := by
          refine GlobalTheory.TopStep.mem_stdAt.2 fun l => ?_
          have e : (((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • (v1 - v)) l =
              ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v1 - A.y0 β P) l - ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v - A.y0 β P) l := by
            simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
          rw [e]
          exact GlobalTheory.TopStep.intAt_sub (h1 l) (h2 l)
        unfold topDat
        congr 1
        have h := GlobalTheory.TopLaw.ftY_comp_glint t.sel (t.tup μ) (t.cst μ) hc P (hok.depthQ P) (κ := 1)
          (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ Yw) v v1 (fun h => absurd h hP)
          (fun _ => hv) (fun h => absurd h hP) (fun _ => hdiff)
        exact h
      rw [frsF_rat_notG t.sel (t.tup μ) p' g' P hP]
      exact key2 _ _ _ (frsF_rat_notG t.sel (t.tup μ) p g P hP) (hrep _ P) (hrep _ P)

end GlobalTheory.TopRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumFixedCongruentFrameChangeTwistPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopStep GlobalTheory.TopLaw GlobalTheory.TopFrameQ

namespace GlobalTheory.TopFrameQM

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu))

theorem topDat_frames_qM {m2 : ℕ} (hm : R.m = m2 + 2) (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hD : 2 * cst.M ≤ cst.D P)
    (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1)))
    (hκ : κ ∈ GLint X.E _ P.1)
    (hκc : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1)
    (hκ' : κ' ∈ GLint X.E _ P.1)
    (hκ'c : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ (2 * cst.M))⁻¹ • (κ' w - w) ∈ stdAt X.E _ P.1)
    (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1)))
    (hy'' : ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) :
    topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
      topDat Ch sel mu cst (m2 + 1) P y y'' := by
  have hM1 : 1 ≤ cst.M := hc.M_pos
  have hMD : cst.M + 1 ≤ cst.D P := by omega
  have hMD' : cst.M + 1 ≤ 2 * cst.M := by omega
  have hq : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
  have hκ's : κ'.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ'
  have hκs : κ.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ
  have hκ'sc := cong_symm hκ' hκ'c
  by_cases hg : ∀ j, abelian₂ P.1 (R.N (m2 + 1 + 1)) cst.M (y (Pi.single j 1))
  · unfold topDat
    congr 1
    · unfold PhiTopG
      rw [if_neg hP]
      have hc0 : cOf R (m2 + 1) = 0 := cOf_topB hm
      have hw : ∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ∀ l : Fin (R.N (m2 + 1 + 1)), l.1 + 1 < R.N (m2 + 1 + 1) →
          IntAt P.1 ((κ'.symm (y (κ w)) - y w) l / (qOf P.1 : X.E)) := by
        intro w hw l hl
        have hu := abelian₂.of_basis y hg (glint_mem (⟨κ, hκ⟩ : GLint X.E _ P.1) hw)
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc hMD' hu).2 l
        have e1 := intAt_inv_pow_le (a := 1) (by omega) d1
        have hu' : ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1 := hκc w hw
        have hyu := (abelian₂.of_basis y hg hu').2 l hl
        rw [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at hyu
        have e2 := intAt_inv_pow_le (a := 1) (by omega) hyu
        rw [pow_one] at e1 e2
        have e3 := e1.add e2
        rw [← add_div] at e3
        convert e3 using 2
        simp only [Pi.sub_apply]
        ring
      have key := fun z hz => GlobalTheory.TopInv.PhiQ_add (K := X.K) (GlobalTheory.TopInv.qOf_mem P.1) hq
        (resChar (mu : Chr X.F X.E X.K) P.1) R.k R.r (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.N (m2 + 1 + 1) - 1) hc0
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) z hz
      refine (congrArg _ (add_sub_cancel _ _)).symm.trans (key _ ?_)
      intro s l
      have hws : (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s (1 : X.E)) : Sp X.E _) ∈
          stdAt X.E (R.N (m2 + 1)) P.1 :=
        mem_stdAt.2 fun a => GlobalTheory.TopInv.single_int s (Fin.castAdd _ a)
      have := hw _ hws ⟨l.1, by omega⟩ (by show l.1 + 1 < _; omega)
      exact this
    · have h1 := ftY_comp_glint sel mu cst hc P (fun _ => hD) ⟨κ, hκ⟩
          (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) y'' (κ.symm y'')
          (fun h => absurd h hP) (fun _ => hy'') (fun h => absurd h hP)
          (fun _ => by
            show ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ (κ.symm y'') - y'') ∈ _
            rw [LinearEquiv.apply_symm_apply, sub_self, smul_zero]
            exact zero_mem _)
      refine h1.trans ?_
      have hy''s : ((qOf P.1 : X.E) ^ cst.M) • y'' ∈ stdAt X.E _ P.1 :=
        mem_stdAt.2 fun l => by simpa only [Pi.smul_apply, smul_eq_mul] using hy'' l
      have hδ : ∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ *
          ((atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) -
            atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) (Pi.single i 1)) := by
        intro i
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc (v := y (Pi.single i 1)) hMD' (hg i)).2
        have e1 : ∀ l, IntAt P.1 ((κ'.symm (y (Pi.single i 1)) - y (Pi.single i 1)) l / (qOf P.1 : X.E) ^ cst.M) :=
          fun l => intAt_inv_pow_le (by omega) (d1 l)
        have e2 := GlobalTheory.TopInv.atNL_int (R.N (m2 + 1 + 1) - 1) _ _ e1
        rw [inv_mul_eq_div]
        convert e2 using 2
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
        rfl
      have h2 := GlobalTheory.ftY_pert_qM sel mu cst hc P hP hD (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y)
        _ y'' hδ hy''s
      rw [add_sub_cancel] at h2
      exact h2
  · have h0 : topDat Ch sel mu cst (m2 + 1) P y y'' = 0 := by
      by_contra hne
      exact hg (lam_of_topDat_ne Ch sel mu cst _ P hP y y'' hne)
    rw [h0]
    by_contra hne
    apply hg
    have h1 := lam_of_topDat_ne Ch sel mu cst _ P hP _ _ hne
    have h2 := lam_comp hκs hκ' hκ'c hMD' _ h1
    intro j
    have := h2 j
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using this

end Main

example : (∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) {m2 : ℕ}, R.m = m2 + 2 → cst.Ok → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  2 * cst.M ≤ cst.D P →
  ∀ (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))),
  κ ∈ GLint X.E (R.N (m2 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E (R.N (m2 + 1)) P.1) →
  κ' ∈ GLint X.E (R.N (m2 + 1 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1, ((qOf P.1 : X.E) ^ (2 * cst.M))⁻¹ • (κ' w - w) ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1) →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) →
  topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat Ch sel mu cst (m2 + 1) P y y'') := by
  intro X Pr R Ch sel S mu cst m2 hm hc P hP hD κ κ' hκ hκc hκ' hκ'c y y'' hy''
  exact topDat_frames_qM Ch sel mu cst hm hc P hP hD κ κ' hκ hκc hκ' hκ'c y y'' hy''

end GlobalTheory.TopFrameQM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTwistPrimeInvariantCongruentFramesStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepDatum_twistPrime_invariant_congruentFrames : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (κ : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))
    (κ' : Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1))),
  κ ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ w - w) ∈ stdAt t.X.E _ P.1) →
  κ' ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ' w - w) ∈ stdAt t.X.E _ P.1) →
  ∀ (y : HomE t.X.E (D.R.N (t.m2 + 1)) (D.R.N (t.m2 + 1 + 1))) (y'' : Sp t.X.E (D.R.N (t.m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * y'' l)) →
  topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'') := by
  first | exact @GlobalTheory.TopFrameQ.topDat_frames_tie | exact GlobalTheory.TopFrameQ.topDat_frames_tie | (intros; apply GlobalTheory.TopFrameQ.topDat_frames_tie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelFrameLiftUnitaryAutNearAdelicMatrixDepthOneStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFrameLift_unitaryAut_near_adelicMatrix_depth_one : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E n ST SG) (w : SG) (g : UF X.E n), ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → ∀ (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), NearAt (seamP s w.1) 1 y (seamGL s (d.1.liftFr w)) → NearAt (seamP s w.1) 1 (ratA D.host.F (seamGL s g.1) * y) (seamGL s (((g, (1 : GLG X.E n SG)) • d).1.liftFr w)) := by
  first | exact @GlobalTheory.FrameRat.nearAt_liftFr_smul | exact GlobalTheory.FrameRat.nearAt_liftFr_smul | (intros; apply GlobalTheory.FrameRat.nearAt_liftFr_smul <;> assumption)
end

