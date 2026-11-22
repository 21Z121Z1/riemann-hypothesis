import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantsThetaComparisonAllTuples
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellCoordinatePolynomialsSurjective
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.CellGen

variable {S : Type} [CommRing S] {m a k b N : ℕ}

theorem pair_gvec (D c : Fin m → Fin (N + 1) → S) (h : LeftInv D c) (w : GPm m a b) (x : GVar m a k b → S)
    (j l : Fin m) : ∑ r, D (w.1 j) r * gvec c w x l r = gcell x j l := by
  simp only [gvec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : ∀ i, ∑ r, D (w.1 j) r * (gcell x i l * c (w.1 i) r) = if j = i then gcell x i l else 0 := by
    intro i
    have h1 : ∑ r, D (w.1 j) r * (gcell x i l * c (w.1 i) r) = gcell x i l * ∑ r, D (w.1 j) r * c (w.1 i) r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [h1, h]
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  simp only [e, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem det_updateCol_one (j : Fin k) (v : Fin k → S) :
    (Matrix.updateCol (1 : Matrix (Fin k) (Fin k) S) j v).det = v j := by
  rw [← Matrix.cramer_apply, Matrix.cramer_one]
  rfl

theorem gcell_castLE (hk : k ≤ m) (x : GVar m a k b → S) (l l' : Fin k) :
    gcell x (Fin.castLE hk l') (Fin.castLE hk l) = (1 : Matrix (Fin k) (Fin k) S) l l' := by
  have h1 : ¬ k ≤ (l' : ℕ) := not_le.2 l'.2
  unfold gcell
  rw [dif_neg (fun h => h1 h.2.2.1), Matrix.one_apply]
  by_cases h : l = l'
  · simp [h]
  · rw [if_neg h, if_neg fun e => h (Fin.castLE_injective hk e).symm]

theorem lform_gxi (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → S) (h : LeftInv D c) (w : GPm m a b) (j : Fin k → Fin m) :
    ∑ q, (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S) (lform D (w.1 ∘ j) q) * gxi a b hk c w q =
      (Matrix.of fun l l' => gcell (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) S) (j l')
        (Fin.castLE hk l)).det := by
  have h1 : ∀ q, (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S) (lform D (w.1 ∘ j) q) =
      lform (fun z => (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S) ∘ D z) (w.1 ∘ j) q := fun q => by
    simp only [lform, map_prod, Function.comp_apply]
  simp only [h1, gxi]
  rw [GlobalTheory.FlagEmb.CauchyBinet.lform_plk]
  congr 1
  ext1 l l'
  exact pair_gvec _ _ (h.map (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S)) w _ (j l') _

theorem lform_gxi_var (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → S) (h : LeftInv D c) (w : GPm m a b) (v : GVar m a k b) :
    ∑ q, (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S)
      (lform D (w.1 ∘ Function.update (Fin.castLE hk) ⟨v.1.2, v.2.2.1⟩ v.1.1) q) * gxi a b hk c w q =
      MvPolynomial.X v := by
  rw [lform_gxi hk D c h w]
  have h1 : (Matrix.of fun l l' => gcell (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) S)
      (Function.update (Fin.castLE hk) ⟨v.1.2, v.2.2.1⟩ v.1.1 l') (Fin.castLE hk l)) =
      Matrix.updateCol (1 : Matrix (Fin k) (Fin k) _) ⟨v.1.2, v.2.2.1⟩
        fun l => gcell MvPolynomial.X v.1.1 (Fin.castLE hk l) := by
    ext1 l l'
    rw [Matrix.of_apply, Matrix.updateCol_apply]
    by_cases hl : l' = ⟨v.1.2, v.2.2.1⟩
    · rw [if_pos hl, hl, Function.update_self]
    · rw [if_neg hl, Function.update_of_ne hl, gcell_castLE]
  rw [h1, det_updateCol_one]
  exact dif_pos v.2

theorem main : ∀ (R : Type) [CommRing R] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R) (w : GPm m a b), a ≤ k → k ≤ b → LeftInv D c → ∑ q, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D w q) * gxi a b hk c w q = 1 ∧ Function.Surjective (MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gxi a b hk c w)) := by
  intro R _ m a k b N hk D c w _ _ h
  refine ⟨?_, fun p => ?_⟩
  · unfold gell
    rw [lform_gxi hk D c h w, ← Matrix.det_one (n := Fin k)]
    congr 1
    ext1 l l'
    exact gcell_castLE hk _ l l'
  · change p ∈ (MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gxi a b hk c w)).range
    induction p using MvPolynomial.induction_on with
    | C r => exact ⟨MvPolynomial.C r, by simp⟩
    | add p q hp hq => exact add_mem hp hq
    | mul_X p v hp =>
      refine mul_mem hp ?_
      rw [← lform_gxi_var hk D c h w v]
      exact sum_mem fun q _ => mul_mem ⟨MvPolynomial.C _, MvPolynomial.eval₂Hom_C _ _ _⟩
        ⟨MvPolynomial.X q, MvPolynomial.eval₂Hom_X' _ _ _⟩

end GlobalTheory.GrCl.CellGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmIdempotentAddStarEqOne
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.ArcBuild

open GlobalTheory.TauTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {T : CDVR} {t : SAB H (Sp T.V)} (P : PELUnif (maximalIdeal T.V) t) {ϖ : T.V} (hϖ : Irreducible ϖ)

def qv : P.D.toPre.X → ℤ := fun χ => (QForm.exists_QVal hϖ P.D χ).choose

theorem isQ_qv : QForm.IsQ P.D.toPre ϖ (qv P hϖ) := fun χ => (QForm.exists_QVal hϖ P.D χ).choose_spec

def beF : LinearMap.BilinForm ℤ P.D.toPre.X :=
  LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D (isQ_qv P hϖ) a b)
    (fun a a' b => by simp [map_add]) (fun n a b => by simp [map_zsmul])
    (fun a b b' => by simp [map_add]) (fun n a b => by simp [map_zsmul])

theorem beF_symm (a b : P.D.toPre.X) : beF P hϖ a b = beF P hϖ b a := QForm.bOf_comm P.D a b

theorem beF_self (a : P.D.toPre.X) : beF P hϖ a a = 2 * qv P hϖ a :=
  (QForm.two_Q_eq hϖ P.D (isQ_qv P hϖ) a).symm

theorem beF_pos {a : P.D.toPre.X} (ha : a ≠ 0) : 0 < beF P hϖ a a := by
  have := QForm.Q_pos hϖ P.D (isQ_qv P hϖ) ha
  rw [beF_self]; omega

theorem beF_adj (x : 𝓞 E) (a b : P.D.toPre.X) : beF P hϖ (x • a) b = beF P hϖ a (H.bar x • b) :=
  letI := H.starRing
  QForm.bOf_balance hϖ P.D GlobalTheory.abelianSchemeLaws_all.1 P.oD (isQ_qv P hϖ) x a b

theorem beF_w0 (a : P.D.toPre.X) : beF P hϖ a (H.w0 • a) = qv P hϖ a := by
  have h₁ := beF_adj P hϖ H.w0 a a
  have hb : H.bar H.w0 = 1 - H.w0 := by rw [HostModel.cmHost_bar_halfIntegerGenerator]
  rw [hb, sub_smul, one_smul, map_sub, beF_symm P hϖ (H.w0 • a) a] at h₁
  have h₂ := beF_self P hϖ a
  omega

def piK : (FractionRing T.V)ˣ :=
  Units.mk0 (algebraMap T.V (FractionRing T.V) ϖ)
    ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)

def tF (a b : P.D.toPre.X) : (FractionRing T.V)ˣ := piK hϖ ^ (-(beF P hϖ a b))

theorem isScalarForm_tF : letI := H.starRing; IsScalarForm (𝓞 E) (tF P hϖ) := by
  letI := H.starRing
  refine ⟨fun a b b' => ?_, fun a b => ?_, fun x a b => ?_⟩
  · simp only [tF, map_add, neg_add, zpow_add]
  · rw [tF, tF, beF_symm]
  · rw [tF, tF, beF_adj]; rfl

theorem cmIdempotent_add_star_eq_one : letI := H.starRing; H.w0 + star H.w0 = 1 := halfUnit_add_star H

abbrev D0 : DegPre T.V := letI := H.starRing; GlobalTheory.TauTwist.twist P.D.toPre H.w0 (tF P hϖ)

def oa0 : letI := H.starRing; (D0 P hϖ).OAct (𝓞 E) :=
  letI := H.starRing; twistAct (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ) P.oD

theorem gen0 (a : P.D.toPre.X) : PsiUnitOn (D0 P hϖ) a Set.univ :=
  psiUnitOn_rescale_of_qVal T P.D.toPre ϖ hϖ a (qv P hϖ a) (isQ_qv P hϖ a) _ (by
    show ((piK hϖ ^ (-(beF P hϖ a (H.w0 • a))) : (FractionRing T.V)ˣ) : FractionRing T.V) = _
    rw [beF_w0, Units.val_zpow_eq_zpow_val]; rfl)

def rF (k : ℕ) (a b : P.D.toPre.X) : (FractionRing T.V)ˣ := piK hϖ ^ (-(beF P hϖ a b / k))

theorem isRootForm_rF {k : ℕ} (hk : ∀ a b, (k : ℤ) ∣ beF P hϖ a b) :
    letI := H.starRing; IsRootForm (𝓞 E) k (tF P hϖ) (rF P hϖ k) := by
  letI := H.starRing
  refine ⟨⟨fun a b b' => ?_, fun a b => ?_, fun x a b => ?_⟩, fun a b => ?_⟩
  · simp only [rF, map_add]
    rw [Int.add_ediv_of_dvd_left (hk a b), neg_add, zpow_add]
  · rw [rF, rF, beF_symm]
  · rw [rF, rF, beF_adj]; rfl
  · rw [rF, tF, ← zpow_natCast, ← zpow_mul, neg_mul, Int.ediv_mul_cancel (hk a b)]
    ext; simp

theorem psiRel0 : letI := H.starRing; PsiRel P.D.toPre (D0 P hϖ).psi fun y => tF P hϖ y (H.w0 • y) :=
  psiRel_rescale _ _

section ThetaShiftProofs

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  (Y : Model Xo c β) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (m : SABMap t Y.t y)

theorem dvd_of_dvd {k : ℕ} (hk : k ∣ l.M') (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF P hϖ a a') (a a' : P.D.toPre.X) :
    (k : ℤ) ∣ beF P hϖ a a' :=
  (Int.natCast_dvd_natCast.2 hk).trans ((dvd_mul_left _ _).trans (hdiv a a'))

def twistedLevelPointsOfLattice (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF P hϖ a a') (hL : GlobalTheory.ArcExt.LevelReps Y y t m P) (v : D.La) :
    QkPt (D0 P hϖ) (FractionRing T.V) l.A :=
  letI := H.starRing
  qkScale (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ) (psiRel0 P hϖ)
    (isRootForm_rF P hϖ (dvd_of_dvd P hϖ (Nat.dvd_lcm_right l.M l.A) hdiv)) _ (hL.1 v).choose

open Classical in

def eta0 (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF P hϖ a a') (hL : GlobalTheory.ArcExt.LevelReps Y y t m P) (v : D.La) :
    QkPt (D0 P hϖ) (FractionRing T.V) l.M :=
  letI := H.starRing
  if hv : v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) then
    qkScale (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ) (psiRel0 P hϖ)
      (isRootForm_rF P hϖ (dvd_of_dvd P hϖ (Nat.dvd_lcm_left l.M l.A) hdiv)) _ ((hL.2 v hv).choose)
  else GlobalTheory.TorusExt.qkZero (tauBimult_twist (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ) P.D.tau_bimult) _ l.M

open scoped Classical in
variable (D β) in

def LieCl : Prop :=
  letI := H.starRing
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (r : O), ((β r : c.F) : ℂ) = H.rt0 →
    ∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct P.oD.onB.toRingAct)
      (spMap ((algebraMap (FractionRing T.V) F).comp (algebraMap T.V _))) τ n ∧
      n + Module.finrank (𝓞 E) P.D.toPre.X =
        if τ H.rt = (algebraMap (FractionRing T.V) F).comp (algebraMap T.V _) (b r) then D.p else D.q

def TateCl (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF P hϖ a a') (hL : GlobalTheory.ArcExt.LevelReps Y y t m P) : Prop :=
  letI := H.starRing
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A →
    ∃ I : TateIsoQ D (D0 P hϖ) (oa0 P hϖ) F,
      (I.ζ l.A : F) = (algebraMap (FractionRing T.V) F).comp (algebraMap T.V _) (b z) ∧
      (∀ a q, QkExt (algebraMap _ F) (twistedLevelPointsOfLattice P hϖ Y y m hdiv hL a) q → Out.QkPt.Equiv (D0 P hϖ) F q (I.ev l.A a)) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∀ q,
        QkExt (algebraMap _ F) (eta0 P hϖ Y y m hdiv hL a) q → Out.QkPt.Equiv (D0 P hϖ) F q (I.ev l.M a)

def arc (hX : Nontrivial P.D.toPre.X) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF P hϖ a a')
    (hL : GlobalTheory.ArcExt.LevelReps Y y t m P) (hLie : LieCl P D β b) (hTate : TateCl P hϖ Y b y m hdiv hL) :
    ArcIn D l β T.V b :=
  letI := H.starRing
  { D₀ := D0 P hϖ
    oa := oa0 P hϖ
    nontriv := hX
    even := psiEven_twist (isScalarForm_tF P hϖ) H.w0 P.D.psi_even
    bimult := tauBimult_twist (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ) P.D.tau_bimult
    gen := gen0 P hϖ
    w0 := psi_weight_zero_twist (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ) P.w0
    be := beF P hϖ
    be_symm := beF_symm P hϖ
    be_pos := fun a ha => beF_pos P hϖ ha
    be_adj := beF_adj P hϖ
    be_dvd := hdiv
    eta := eta0 P hϖ Y y m hdiv hL
    etaA := twistedLevelPointsOfLattice P hϖ Y y m hdiv hL
    geom := fun F _ _ _ r z hr hz f hf => by
      subst hf
      obtain ⟨I, h₁, h₂, h₃⟩ := hTate F z hz
      exact ⟨hLie F r hr, I, h₁, h₂, h₃⟩ }

theorem arc_D₀ (hX) (hdiv) (hL) (hLie) (hTate) : (arc P hϖ Y b y m hX hdiv hL hLie hTate).D₀ = D0 P hϖ := rfl

end ThetaShiftProofs

end GlobalTheory.ArcBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombSnd
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcLieCoord

attribute [local instance] Over.cartesianMonoidalCategory

open MonoidalCategory CartesianMonoidalCategory MonObj Filter GlobalTheory.ArcLie

section Group

variable {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G]
  [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem tan_le (h : IsGrpPullback G' G x φ) (w : epsR S ⟶ G') (hw : IsTangent w) (V : G.left.Opens)
    (hV : ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V) : ⊤ ≤ (w.left ≫ φ) ⁻¹ᵁ V := by
  unfold IsTangent at hw
  rw [GlobalTheory.ArcLie.le_iff_fst, ← Category.assoc, hw]
  exact hV

theorem comb_snd [IsCommMonObj G'] (h : IsGrpPullback G' G x φ) {n : ℕ} (v : Fin n → (epsR S ⟶ G'))
    (hv : ∀ k, IsTangent (v k)) (c : Fin n → S) (w : epsR S ⟶ G') (hc : IsLieComb c v w) (V : G.left.Opens)
    (hV : ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V) (f : Γ(G.left, V)) :
    (valR (w.left ≫ φ) V f).snd = ∑ k, c k * (valR ((v k).left ≫ φ) V f).snd := by
  obtain ⟨u, hu, hp⟩ := (ReciprocityTheory.ChartRestriction.G.Chart.comb_push h c v w).1 hc
  have e1 : (show Sp S ⟶ G'.left from (1 : Over.mk (𝟙 (Sp S)) ⟶ G').left) = (η[G']).left := by
    have : (1 : Over.mk (𝟙 (Sp S)) ⟶ G') = η[G'] := by
      rfl
    rw [this]
  have key := GlobalTheory.ArcLie.snd_comb_lift h (x' := 𝟙 (Sp S)) (Category.id_comp x) (fun k => (v k).left)
    (fun k => by rw [Category.comp_id]; exact Over.w (v k)) (fun k => (ReciprocityTheory.ChartRestriction.G.Chart.tan_push h (v k)).1 (hv k))
    c w.left (by rw [Category.comp_id]; exact Over.w w) u hu hp (φ ⁻¹ᵁ V) (by rw [e1]; exact hV) ((φ.app V).hom f)
  rw [GlobalTheory.HolHom.valR_comp, key]
  exact Finset.sum_congr rfl fun k _ => by rw [GlobalTheory.HolHom.valR_comp]

end Group

end GlobalTheory.ArcLieCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagNeZeroOfTriangularIndependentStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diag_ne_zero_of_triangular_independent : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (ι : Type) (c c' : Let m → ι → K) (d : Let m → K), (∀ τ, LinearIndependent K fun j : Fin (m τ) => c' ⟨τ, j⟩) → Tri c c' d → ∀ z, d z ≠ 0 := by
  first | exact @GlobalTheory.FlagEmb.tri_diag_ne_zero | exact GlobalTheory.FlagEmb.tri_diag_ne_zero | (intros; apply GlobalTheory.FlagEmb.tri_diag_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedEmbedding
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

theorem basAt_basAt_tau {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {Z : Scheme.{0}} {π : Z ⟶ X} {U U' : Z.Opens}
    {hU : IsAffineOpen U} (hU' : IsAffineOpen U') (le : U' ≤ U) {κ : Type} [Finite κ]
    (b : Module.Basis κ Γ(Z, U) (TanM (tau hU ≫ π) t.G)) (w : Sp S ⟶ Z) (hw : ⊤ ≤ w ⁻¹ᵁ U') :
    basAt (hU := hU') (basAt b (tau hU') (tau_le hU' le)) w hw =
      basAt b w (le_preimage_mono le hw) := by
  refine Module.Basis.eq_of_apply_eq fun i => ?_
  rw [basAt, basPull_apply]
  exact tanPull_basAt b _ _ _ (by rw [tau, spMap_ev]) _ _ i

theorem exists_adapted_emb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ), Geo M π → Nonempty (Adapted A σ k) → ∃ (D : Adapted A σ k) (N : ℕ), Nonempty (D.C.Emb N) := by
  intro E _ _ _ H Dw l Xo c V _ M X π ty A σ k hG ⟨D⟩
  obtain ⟨Γ, a, B, aff, cover, le, N, hN⟩ := GlobalTheory.T.exists_refined_cocycle_embedding V X (π ≫ M.s) hG.proj D.C
  refine ⟨{ C := D.C.refine a B aff cover le
            b := fun g => basAt (D.b (a g)) (tau (aff g)) (tau_le (aff g) (le g))
            int := fun g K _ w hw u hu j hj => ?_
            coord := fun g d S _ z hg hd v => ?_ }, N, hN⟩
  · have := D.int (a g) K w (le_preimage_mono (le g) hw) u hu j hj
    rw [← basAt_basAt_tau (aff g) (le g) (D.b (a g)) w hw] at this
    exact this
  · have := D.coord (a g) (a d) S z (le_preimage_mono (le g) hg) (le_preimage_mono (le d) hd) v
    rw [← D.C.refine_tr a B aff cover le g d z hg hd] at this
    unfold crd at this
    rw [← basAt_basAt_tau (aff g) (le g) (D.b (a g)) z hg, ← basAt_basAt_tau (aff d) (le d) (D.b (a d)) z hd] at this
    exact this

end GlobalTheory.DRFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableTangentBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_stable_tangent_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (x : X), ∃ (U : X.affineOpens) (n : ℕ) (v : Fin n → Tn t Γ(X, U.1)), x ∈ U.1 ∧ StabBasis t U.2.fromSpec v := by
  first | exact @GlobalTheory.FlagEmb.Stab.exists_stabBasis | exact GlobalTheory.FlagEmb.Stab.exists_stabBasis | (intros; apply GlobalTheory.FlagEmb.Stab.exists_stabBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_tangent_basis_locally : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (S : Scheme.{0}) (ρ : S ⟶ X) (z : S), ∃ (V : S.affineOpens) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(S, V.1)) ⟶ t.G.left)), z ∈ V.1 ∧ IsTanBasis t (R := Γ(S, V.1)) (V.2.fromSpec ≫ ρ) e := by
  first | exact @GlobalTheory.LineNorm.exists_affine_isTanBasis | exact GlobalTheory.LineNorm.exists_affine_isTanBasis | (intros; apply GlobalTheory.LineNorm.exists_affine_isTanBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuumStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_dvr_local_extension_of_countable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R], Countable R → ∃ (T : CDVR) (i : R →+* T.V), Function.Injective i ∧ IsLocalHom i ∧ Cardinal.mk T.V ≤ Cardinal.continuum := by
  first | exact @GlobalTheory.CountableCompletion.exists_cdvr_mk_le_continuum | exact GlobalTheory.CountableCompletion.exists_cdvr_mk_le_continuum | (intros; apply GlobalTheory.CountableCompletion.exists_cdvr_mk_le_continuum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChainChartLocalUnitCharacterCompatibleLeveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chainChart_localUnitCharacter_compatible_level : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        ∃ ψ : Formalism.L2.G.awayG (w.D Z).sp.cm.sig ((w.D Z).sp.X (j + 1)).gram
            (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Uloc ((w.D Z).what₂.places.resChar v) →* ((w.D Z).gat u v hg).Oˣ,
          Formalism.MainNotions.G.CmpJ.UnitCharacterChartCompatibility hj (tt.forms.ch u ((w.D Z).what₂.muAt v) hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev (t.cmp.embW u v hg) ψ := by
  first | exact @GlobalTheory.Mem.Top.KerTwPsi.psi_tied | exact GlobalTheory.Mem.Top.KerTwPsi.psi_tied | (intros; apply GlobalTheory.Mem.Top.KerTwPsi.psi_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantLieBasisAnalyticBasisArc
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ArcLieFrame

theorem exists_const_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), ∃ (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ), (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) ∧ IsLieBasis v ∧ (Matrix.of z).det ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha
  have hG := GlobalTheory.SemiRigid.globalFns
  obtain ⟨g', e, v, -, hev, hb, hu, -⟩ := GlobalTheory.ConstLie.exists_const_basis hG E H Dw l Xo c V V.subtype Y ℂ
    (σ.comp V.subtype) a χ W
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.ExpTan.anVec_bijective hG E H Dw l Xo c σ V V.subtype Y a χ W g ty Fu Ha
  choose z hz using fun i => (h1 (e i) (hev i).1).exists
  have hli : LinearIndependent ℂ z := by
    rw [Fintype.linearIndependent_iff]
    intro cf hcf
    obtain ⟨ν, hν⟩ := GlobalTheory.ConstLie.exists_gtComb cf e
    obtain ⟨ν₀, hν₀⟩ := GlobalTheory.ConstLie.exists_gtComb (0 : Fin g' → ℂ) e
    have a1 := (h4 g' cf e z ν hz).1 hν
    have a0 := (h4 g' 0 e z ν₀ hz).1 hν₀
    rw [hcf] at a1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at a0
    obtain rfl : ν = ν₀ := (h2 0).unique a1 a0
    have ht := h3 _ _ a1
    have := (hu ν ht).unique hν hν₀
    exact fun i => congrFun this i
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range z) := by
    intro z₀ _
    rw [Submodule.mem_span_range_iff_exists_fun]
    obtain ⟨ν, hν, -⟩ := h2 z₀
    obtain ⟨cf, hcf, -⟩ := hu ν (h3 _ _ hν)
    exact ⟨cf, (h1 ν (h3 _ _ hν)).unique ((h4 g' cf e z ν hz).1 hcf) hν⟩
  have hg : g' = g := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    simpa using this.symm
  subst hg
  refine ⟨e, v, z, fun k => ⟨(hev k).2, hz k⟩, hb, ?_⟩
  have hu' : IsUnit (Matrix.of z) := (Matrix.linearIndependent_rows_iff_isUnit).1 (by simpa using hli)
  exact (Matrix.isUnit_iff_isUnit_det _).1 hu' |>.ne_zero

end GlobalTheory.ArcLieFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantsThetaComparisonAllTuplesStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constants_theta_comparison_all_tuples : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), PreChar R → TieIn T R κ v₀ → T.pb = R.C.P.pb → Finite T0 → QGuard R → IoExt R → ∀ i, VStd D i → OMPins T R κ v₀ O i → ∃ cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc 1 ∧ ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧ O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧ O'.OneMapOf (κ i) (v₀ i (sg0 D A)) cc 1 := by
  first | exact @GlobalTheory.RealGeo.exists_const_oneMapOf_all | exact GlobalTheory.RealGeo.exists_const_oneMapOf_all | (intros; apply GlobalTheory.RealGeo.exists_const_oneMapOf_all <;> assumption)
end

