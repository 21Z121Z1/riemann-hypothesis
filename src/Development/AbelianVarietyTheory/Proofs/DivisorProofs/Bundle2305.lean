import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentPullbackComplexDualNumbers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanPull

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel in
set_option maxHeartbeats 1000000 in

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR V)), GtTan gm₀ → ∃ gm : GtPt D (TE V C), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm ∧ (∃ o : GtPtF D C, o.IsZero ∧ GtPt.IsPullF C (redE C) gm o) ∧ (gm₀.b = DegPre.zeroT D (epsR V) → gm.b = DegPre.zeroT D (TE V C)) ∧ ∀ (a : V) (χ : D.X), (∀ (Z : Scheme.{0}) (q : Z ⟶ (epsR V).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm₀.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom (1 + TrivSqZeroExt.inr a))) → vE (gm.s χ) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr (toF V C a) := by
  intro V _ _ D C _ _ N ν gm₀ htan
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨H, _, _, hH⟩ := exists_isGt hG (splitExt D)
  obtain ⟨Φ, hp, ha⟩ := exists_points hG hH
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GtVec.isZero_of_isAdd (by simpa using ha T 1 1)
  have hTF : spMap (toF V C) = (TF (R := V) C).hom := by
    simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hTE : spMap (dualMap (toF V C)) ≫ (epsR V).hom = (TE V C).hom := by
    rw [TanLift.dualMap_over, hTF]; rfl
  let hh : TE V C ⟶ epsR V := Over.homMk (spMap (dualMap (toF V C))) hTE
  obtain ⟨x₀, rfl⟩ := (Φ (epsR V)).surjective gm₀
  refine ⟨Φ _ (hh ≫ x₀), hp _ _ hh x₀, ?_, ?_, ?_⟩
  · obtain ⟨o₀, ho₀, hpo⟩ := htan
    let r : baseOver (Sp V) ⟶ epsR V := Over.homMk (redE V) (TanLift.redE_over V)
    have e₀ : o₀ = Φ _ (r ≫ x₀) := isPull_unique hpo (hp _ _ r x₀)
    have e₁ : r ≫ x₀ = 1 := (Φ _).injective ((e₀.symm.trans (GtVec.isZero_unique ho₀ (hz _))))
    let k : TF (R := V) C ⟶ TE V C := Over.homMk (redE C) (by
      show redE C ≫ spMap (algebraMap C (DualNumber C)) ≫ (TF (R := V) C).hom = (TF (R := V) C).hom
      rw [← Category.assoc, GtVec.red_comp, Category.id_comp])
    let tf : TF (R := V) C ⟶ baseOver (Sp V) := Over.homMk (TF (R := V) C).hom (Category.comp_id _)
    have e₂ : k ≫ hh = tf ≫ r := by
      ext
      show redE C ≫ spMap (dualMap (toF V C)) = (TF (R := V) C).hom ≫ redE V
      rw [← hTF]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    have e₃ : k ≫ hh ≫ x₀ = 1 := by
      rw [← Category.assoc, e₂, Category.assoc, e₁, MonObj.comp_one]
    have hpk := hp _ _ k (hh ≫ x₀)
    rw [e₃] at hpk
    let g := Φ (TF (R := V) C) 1
    refine ⟨⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩, ⟨(hz _).1, (hz _).2⟩, hpk⟩
  · intro hb
    have e := ((TorusModel.isPull_iff _ _ _).1 (hp _ _ hh x₀)).1
    rw [e, hb]
    simp
  · intro a χ hval
    have hloc : IsLocalRing (DualNumber C) := TanLift.isLocalRing_dualNumber C
    have hlocH : IsLocalHom (TrivSqZeroExt.fstHom C C C).toRingHom :=
      ⟨fun x hx => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 hx⟩
    set gm := Φ _ (hh ≫ x₀)
    let J' : (Sp (DualNumber C) ⟶ D.P.A.left) → D.P.L.ι := fun ψ => ν.J (redE C ≫ ψ)
    have hJ' : Good D.P.L (cpt (DualNumber C)) J' := fun ψ => by
      have h1 := ν.good (redE C ≫ ψ) (show cpt C ∈ (⊤ : (Sp C).Opens) from trivial)
      have hc : (redE C) (cpt C) = cpt (DualNumber C) :=
        IsLocalRing.comap_closedPoint (TrivSqZeroExt.fstHom C C C).toRingHom
      have h2 : ψ ((redE C) (cpt C)) ∈ D.P.L.U (J' ψ) := h1
      rw [hc] at h2
      exact h2
    have ht := (top_le_iff_cpt (𝟙 (Sp (DualNumber C))) _).2 (hJ'.mem (DegPre.gtφT D (TE V C) gm.b χ) (𝟙 _))
    apply toStkA_injective (A := DualNumber C)
    have l1 := toStkA_valR (𝟙 (Sp (DualNumber C))) _ (cpt (DualNumber C)) ht ((gm.s χ).s _)
    have l2 := (val_corr hJ' ((hp _ _ hh x₀).2 χ) (𝟙 _)).trans (val_pull hJ' _ _ _)
    have l3 := hval _ (𝟙 _ ≫ hh.left) _ _ hJ'
    have hv1 : valR (𝟙 (Sp (DualNumber V))) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom
        (1 + TrivSqZeroExt.inr a)) = 1 + TrivSqZeroExt.inr a := by
      have h0 : ⊤ ≤ 𝟙 (Sp (DualNumber V)) ⁻¹ᵁ ⊤ := fun _ _ => trivial
      rw [valR, dif_pos h0]
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
      erw [show (homOfLE h0) = 𝟙 (⊤ : (Sp (DualNumber V)).Opens) from rfl]
      simp
    have l4 := FormalValue.toStkA_map_valR (dualMap (toF V C)) (𝟙 (Sp (DualNumber V))) ⊤ (cpt (DualNumber C))
      (fun _ _ => trivial) ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom (1 + TrivSqZeroExt.inr a))
    rw [hv1, Category.comp_id] at l4
    have hd : dualMap (toF V C) (1 + TrivSqZeroExt.inr a) = 1 + TrivSqZeroExt.inr (toF V C a) := by
      ext <;> simp [dualMap]
    rw [hd] at l4
    rw [l4]
    refine l1.trans ?_
    refine (congrArg Units.val l2).trans ?_
    refine l3.trans ?_
    rw [Category.id_comp]
    rfl

end GlobalTheory.MBLow.TanPull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentCombinationCharacterValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TorusVals

variable {R : Type} [CommRing R]

theorem dual_mul (a b : R) : ((1 : DualNumber R) + TrivSqZeroExt.inr a) * (1 + TrivSqZeroExt.inr b) = 1 + TrivSqZeroExt.inr (a + b) := by
  ext <;> simp [add_comm]

theorem epsScaleR_one_add (c a : R) : epsScaleR c (1 + TrivSqZeroExt.inr a) = 1 + TrivSqZeroExt.inr (c * a) := by
  ext <;> simp [epsScaleR, mul_comm]

section Gs

variable {Z : Scheme.{0}} (q : Z ⟶ (epsR R).left) (z : Z)

theorem gs_one_add_zero : gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr 0)) = 1 := by
  rw [gs_eq q z ⊤ trivial, TrivSqZeroExt.inr_zero, add_zero, map_one, map_one, map_one]

theorem gs_dual_mul (a b : R) :
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) *
      gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr b)) =
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a + b))) := by
  rw [← gs_mul q z ⊤ trivial, ← map_mul, dual_mul]

theorem gs_scale (c a : R) :
    gs (q ≫ (epsScale R c).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) =
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (c * a))) := by
  rw [← gs_pull q (epsScale R c).left z ⊤ trivial, ← epsScaleR_one_add]
  have e := congrArg (fun f => f.hom (1 + TrivSqZeroExt.inr a : DualNumber R))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (epsScaleR c)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  rw [e]
  rfl

end Gs

variable [IsDomain R] {D : DegPre R} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H] {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T}

def HasVals (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T) (y : epsR R ⟶ H) (a : D.X → R) : Prop :=
  (Φ _ y).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    (val ((Φ _ y).s χ) q z J).val = gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a χ)))

theorem hasVals_one (hΦ : TorusModel.Represents Φ) : HasVals Φ 1 (fun _ => 0) := by
  have hz : (Φ (epsR R) 1).IsZero := GtVec.isZero_of_isAdd (by simpa using hΦ.2 (epsR R) 1 1)
  refine ⟨hz.1, fun χ Z q z J hJ => ?_⟩
  rw [val_corr hJ (hz.2 χ) q, val_one, gs_one_add_zero]
  rfl

theorem hasVals_scale (hΦ : TorusModel.Represents Φ) {y : epsR R ⟶ H} {a : D.X → R} (h : HasVals Φ y a) (c : R) :
    HasVals Φ (epsScale R c ≫ y) (fun χ => c * a χ) := by
  have hp := hΦ.1 (epsR R) (epsR R) (epsScale R c) y
  refine ⟨?_, fun χ Z q z J hJ => ?_⟩
  · rw [((TorusModel.isPull_iff _ _ _).1 hp).1, h.1]
    simp only [DegPre.zeroT, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  · rw [val_corr hJ (hp.2 χ) q, val_pull hJ, h.2 χ Z _ z J hJ, gs_scale]

theorem hasVals_mul (hΦ : TorusModel.Represents Φ) {y y' : epsR R ⟶ H} {a a' : D.X → R} (h : HasVals Φ y a)
    (h' : HasVals Φ y' a') : HasVals Φ (y * y') (fun χ => a χ + a' χ) := by
  have hs := hΦ.2 (epsR R) y y'
  refine ⟨?_, fun χ Z q z J hJ => ?_⟩
  · rw [((TorusModel.isAdd_iff _ _ _).1 hs).1, h.1, h'.1]
    exact _root_.mul_one _
  · have e := (val_mul hJ _ _ q).symm.trans ((val_corr hJ (hs.2 χ) q).trans (val_mul hJ _ _ q))
    let T' : Over (Sp R) := Over.mk (q ≫ (epsR R).hom)
    let ρ : T' ⟶ epsR R := Over.homMk q rfl
    have hc : val (DegPre.cubAtT D (epsR R) (DegPre.cT D (epsR R) χ) (Φ _ y).b (Φ _ y').b) q z J = 1 := by
      have := val_cub D.cub ρ hJ (DegPre.cT D (epsR R) χ) (Φ _ y).b (Φ _ y').b
      refine this.trans ?_
      rw [h'.1]
      have e1 : ρ ≫ DegPre.zeroT D (epsR R) = (1 : T' ⟶ D.P.A) := by
        simp only [DegPre.zeroT, ← Category.assoc]
        rw [Hom.one_def]
        congr 1
      rw [e1]
      exact (isCub_cubV D.cub hJ).face₃ _ _
    rw [hc, _root_.mul_one] at e
    rw [e, Units.val_mul, h.2 χ Z q z J hJ, h'.2 χ Z q z J hJ, gs_dual_mul]

end GlobalTheory.MBLow.TorusVals

namespace GlobalTheory.MBLow.TorusVals

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H]
  {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T}

theorem hasVals_tanComb (hΦ : TorusModel.Represents Φ) : ∀ (r : ℕ) (a : Fin r → D.X → R) (x : Fin r → (epsR R ⟶ H)),
    (∀ l, HasVals Φ (x l) (a l)) → ∀ d : Fin r → R, HasVals Φ (tanComb d x) (fun χ => ∑ l, d l * a l χ)
  | 0, a, x, _, d => by
    have e : tanComb d x = 1 := by simp [tanComb]
    have ef : (fun χ => ∑ l : Fin 0, d l * a l χ) = fun _ => 0 := funext fun _ => by simp
    rw [e, ef]
    exact hasVals_one hΦ
  | r + 1, a, x, hx, d => by
    have e : tanComb d x = (epsScale R (d 0) ≫ x 0) * tanComb (fun i => d i.succ) (fun i => x i.succ) := by
      simp only [tanComb, List.ofFn_succ, List.prod_cons]
    have key := hasVals_mul hΦ (hasVals_scale hΦ (hx 0) (d 0))
      (hasVals_tanComb hΦ r (fun i => a i.succ) (fun i => x i.succ) (fun l => hx l.succ) (fun i => d i.succ))
    have ef : (fun χ => ∑ l, d l * a l χ) = fun χ => d 0 * a 0 χ + ∑ l : Fin r, d l.succ * a l.succ χ :=
      funext fun χ => Fin.sum_univ_succ _
    rw [e, ef]
    exact key

theorem tanComb_vals : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (a : Fin r → D.X → R) (x : Fin r → (epsR R ⟶ H)), (∀ l, (Φ _ (x l)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x l)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a l χ)))) → ∀ d : Fin r → R, (Φ _ (tanComb d x)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (tanComb d x)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (∑ l, d l * a l χ))) :=
  fun _ _ _ _ _ _ _ _ hΦ r a x hx d => hasVals_tanComb hΦ r a x hx d

end GlobalTheory.MBLow.TorusVals

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageThetaDictionaryExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StageDict

theorem gBig_mono {P Q : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨CF1, h1⟩ := hP
  refine ⟨CF1, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF hCF
  exact ⟨C1, x1, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (g1 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩

theorem stage_dictionary : GBig fun {D} {T} {Lc} {sc} G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ), ∀ t : T,
        GlobalTheory.SquareComm.IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧
        (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧
          HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧
        GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧
        (∀ P g h, thetaKO (X.ω t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧
        ∀ P g h, thetaKO (X.ω' t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  refine gBig_mono GlobalTheory.T.towerStage_seesawDictionary_framesSignatures ?_
  intro D T Lc sc G μ₀ C x b _ H W _ _ _ i j p q A A' WW X hX
  obtain ⟨FA, FA', FW, a, b, -, -, -, h⟩ := H W i j p q A A' WW X hX
  exact ⟨FA, FA', FW, a, b, h⟩

end GlobalTheory.StageDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDvrFormallyUnramifiedOfEtale
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory

theorem formallyUnramified_of_dvr_of_essFiniteType : ∀ (R T V : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing T] [Algebra R T] [Algebra.FormallyUnramified R T] [Algebra.EssFiniteType R T] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra R V] (μ : T →ₐ[R] V), (∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R V r ∈ IsLocalRing.maximalIdeal V) → Function.Injective (algebraMap R V) → (∀ v : V, ∃ a b : T, μ b ≠ 0 ∧ v * μ b = μ a) → Algebra.FormallyUnramified R V := by
  intro R T V _ _ _ _ _ _ _ _ _ _ _ μ hm hinj hfrac
  let Q : Ideal T := (IsLocalRing.maximalIdeal V).comap μ
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  let D := Localization.AtPrime Q
  haveI : Algebra.FormallyUnramified T D := .of_isLocalization Q.primeCompl
  haveI : Algebra.FormallyUnramified R D := .comp R T D
  haveI : Algebra.EssFiniteType T D := .of_isLocalization D Q.primeCompl
  haveI : Algebra.EssFiniteType R D := .comp R T D
  have hQ : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R T r ∈ Q := fun r hr => by
    show μ (algebraMap R T r) ∈ IsLocalRing.maximalIdeal V
    rw [μ.commutes]; exact hm r hr
  haveI : IsLocalHom (algebraMap R D) := ⟨fun r hr => by
    by_contra hnu
    rw [IsScalarTower.algebraMap_apply R T D, IsLocalization.AtPrime.isUnit_to_map_iff D Q] at hr
    exact hr (hQ r ((IsLocalRing.mem_maximalIdeal _).2 hnu))⟩
  have hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R D) = IsLocalRing.maximalIdeal D :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hunit : ∀ y : Q.primeCompl, IsUnit (μ y) := fun y => by
    by_contra h; exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  let ν : D →ₐ[R] V := IsLocalization.liftAlgHom (M := Q.primeCompl) (f := μ) hunit
  have hν : ∀ t, ν (algebraMap T D t) = μ t := fun t => IsLocalization.lift_eq _ _
  have hνu : ∀ d, IsUnit (ν d) → IsUnit d := by
    intro d hd
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl d
    have e : IsLocalization.mk' D x s * algebraMap T D s = algebraMap T D x :=
      IsLocalization.mk'_spec D x s
    have hx : IsUnit (μ x) := by
      have := congrArg ν e
      rw [map_mul, hν, hν] at this
      rw [← this]; exact hd.mul (hunit s)
    have hxQ : x ∈ Q.primeCompl := fun h => (IsLocalRing.mem_maximalIdeal _).1 h hx
    have : IsUnit (algebraMap T D x) := IsLocalization.map_units D (⟨x, hxQ⟩ : Q.primeCompl)
    rw [← e] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmR : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hmD : IsLocalRing.maximalIdeal D = Ideal.span {algebraMap R D ϖ} := by
    rw [← hmax, hmR, Ideal.map_span, Set.image_singleton]
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hS := GlobalTheory.T.subring_eq_univ_of_uniformizer_generates V (ν : D →+* V).range (algebraMap R V ϖ) ⟨algebraMap R D ϖ, ν.commutes ϖ⟩
    ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) (hm ϖ hϖm) ?_ ?_ ?_
  · refine Algebra.FormallyUnramified.of_surjective ν fun v => ?_
    have hv : v ∈ (ν : D →+* V).range := hS ▸ Subring.mem_top v
    obtain ⟨d, hd⟩ := hv
    exact ⟨d, hd⟩
  · rintro _ ⟨d, rfl⟩ hs
    have hu : IsUnit (ν d) := by
      by_contra h; exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨u, hu'⟩ := hνu d hu
    refine ⟨ν ↑u⁻¹, ⟨_, rfl⟩, ?_⟩
    change ν d * ν ↑u⁻¹ = 1
    rw [← map_mul, ← hu', Units.mul_inv, map_one]
  · rintro _ ⟨d, rfl⟩ hs
    have hd : d ∈ IsLocalRing.maximalIdeal D := (IsLocalRing.mem_maximalIdeal _).2 fun h =>
      (IsLocalRing.mem_maximalIdeal _).1 hs (h.map ν)
    rw [hmD] at hd
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hd
    refine ⟨ν a, ⟨a, rfl⟩, ?_⟩
    change ν (a * algebraMap R D ϖ) = _
    rw [map_mul, ν.commutes, mul_comm]
  · intro v
    obtain ⟨a, b, hb, hab⟩ := hfrac v
    exact ⟨μ a, ⟨_, hν a⟩, μ b, ⟨_, hν b⟩, hb, hab⟩

end GlobalTheory

namespace GlobalTheory

theorem trace_dvr_formallyUnramified_of_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ (V : ValuationSubring M.functionField) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap (functionFieldMap f))], DominatesStalk V z → letI := ((functionFieldMap f).restrict (V.comap (functionFieldMap f)) V fun _ hx => hx).toAlgebra; Algebra.FormallyUnramified (V.comap (functionFieldMap f)) V := by
  intro M W _ _ f _ U hU z hz V _ _ hV
  obtain ⟨-, hfe, hess⟩ :=
    stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict M W f U hU z hz
  set φ := functionFieldMap f with hφ
  set R := V.comap φ
  let A := W.presheaf.stalk (f z)
  let B := M.presheaf.stalk z
  let g : A →+* B := (f.stalkMap z).hom
  letI : Algebra A B := g.toAlgebra
  haveI : Algebra.FormallyEtale A B := hfe
  haveI : Algebra.EssFiniteType A B := hess
  have hcomp : ∀ a : A, φ (algebraMap A W.functionField a) = algebraMap B M.functionField (g a) :=
    fun a => functionFieldMap_algebraMap f z a
  have hαR : ∀ a : A, algebraMap A W.functionField a ∈ R := fun a => by
    change φ _ ∈ V
    rw [hcomp]; exact hV.1 _
  let αR : A →+* R := (algebraMap A W.functionField).codRestrict R hαR
  let βV : B →+* V := (algebraMap B M.functionField).codRestrict V hV.1
  letI algRV : Algebra R V := (φ.restrict R V fun _ hx => hx).toAlgebra
  letI : Algebra A R := αR.toAlgebra
  letI : Algebra A V := (βV.comp g).toAlgebra
  haveI : IsScalarTower A R V := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (hcomp a).symm
  let gV : B →ₐ[A] V := { βV with commutes' := fun _ => rfl }
  let μ : TensorProduct A R B →ₐ[R] V :=
    Algebra.TensorProduct.lift (Algebra.ofId R V) gV fun _ _ => Commute.all _ _
  haveI : Algebra.FormallyUnramified R (TensorProduct A R B) := Algebra.FormallyUnramified.base_change R
  haveI : Algebra.EssFiniteType R (TensorProduct A R B) := Algebra.EssFiniteType.baseChange A B R
  refine formallyUnramified_of_dvr_of_essFiniteType R (TensorProduct A R B) V μ ?_ ?_ ?_
  · intro r hr
    by_contra hnu
    have hu : IsUnit (algebraMap R V r) := by
      by_contra h; exact hnu ((IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
    have hw' : φ (r : W.functionField) * (w : M.functionField) = 1 := congrArg Subtype.val hw
    have hr0 : (r : W.functionField) ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hw'; exact zero_ne_one hw'
    have hinv : (r : W.functionField)⁻¹ ∈ R := by
      change φ _ ∈ V
      rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hw']
      exact w.2
    exact (IsLocalRing.mem_maximalIdeal _).1 hr
      (isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hr0)⟩)
  · intro x y hxy
    exact Subtype.ext (φ.injective (congrArg Subtype.val hxy))
  · intro v
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) (v : M.functionField)
    have hμ : ∀ c : B, ((μ (1 ⊗ₜ c) : V) : M.functionField) = algebraMap B M.functionField c := by
      intro c
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
    refine ⟨1 ⊗ₜ a, 1 ⊗ₜ b, ?_, ?_⟩
    · intro h0
      apply nonZeroDivisors.ne_zero hb
      apply IsFractionRing.injective B M.functionField
      rw [map_zero]
      rw [← hμ, h0]; rfl
    · apply Subtype.ext
      rw [Subring.coe_mul, hμ, hμ]
      rw [← hab, div_mul_cancel₀]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedDualPointOfIntegralTorusExtPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedDualPoint_of_integralTorusExtPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (gm₀ : GtPt D (epsR V)) (gm : GtPt D (TE V C)), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ mu : D.X, ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (DegPre.prB D C).left = spMap (dualMap (toF V C)) ≫ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ∧ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ≫ D.P.A.hom = spMap (algebraMap V (DualNumber V)) ∧ ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (fst (TF (R := V) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
  first | exact @GlobalTheory.MBLow.trF_dualPoint_of_isPull | exact GlobalTheory.MBLow.trF_dualPoint_of_isPull | (intros; apply GlobalTheory.MBLow.trF_dualPoint_of_isPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportClassMinimisersAlongLinearEquivStatement
section
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_classMinimisers_along_linearEquiv : ∀ (O : Type) [CommRing O] (X Y : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (n N : ℕ) [NeZero N] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ)) (ebY : Y ≃ₗ[ℤ] (Fin n → ℤ)) (f : X ≃ₗ[O] Y) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((ebY (μ cl) i : ℤ) : ZMod N) = cl i) → ∃ σ : Equiv.Perm (Fin n → ZMod N), (∀ cl i, ((ebX (f.symm (μ (σ cl))) i : ℤ) : ZMod N) = cl i) ∧ ∀ b : LinearMap.BilinForm ℤ Y, (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → pull f.toLinearMap b (f.symm (μ (σ cl))) (f.symm (μ (σ cl))) ≤ pull f.toLinearMap b α α := by
  first | exact @GlobalTheory.transport_minimisers | exact GlobalTheory.transport_minimisers | (intros; apply GlobalTheory.transport_minimisers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPermutedDirectSumComplexificationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_permuted_directSum_complexification : ∀ (Ks LL WL C H G X : Type) [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Group G] [Group H] [Fintype X] [DecidableEq X] [MulAction H X]
    (σ : LL →+* ℂ) (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL), (∀ j, b j ∈ WK) → LinearIndependent Ks b →
    Submodule.span Ks (Set.range b) = WK → LinearIndependent LL b → Submodule.span LL (Set.range b) = ⊤ →
    ∀ (e : C ≃ₗ[Ks] WK) (ρ0 : G →* (WL →ₗ[LL] WL)) (χ : G →* LLˣ) (act : G → C →ₗ[Ks] C),
    (∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) → ∀ (φ : H →* G) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (σ.comp (algebraMap Ks LL)) C)),
    DirectSum.IsInternal A → (∀ (h : H) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (σ.comp (algebraMap Ks LL)) (act (φ h)) v ∈ A (h • y)) →
    ∃ A' : X → Submodule ℂ (GlobalTheory.DefRead.VC σ WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, GlobalTheory.DefRead.twBC σ ρ0 χ (φ h) v ∈ A' (h • y) := by
  first | exact @GlobalTheory.DefRead.Transport.transport | exact GlobalTheory.DefRead.Transport.transport | (intros; apply GlobalTheory.DefRead.Transport.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesAllFramesOfDenseOpenStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transporter_moves_all_frames_of_dense_open : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a) (O : Set (Frame ((uAt r v i).X k).Ψ D.R.r)), IsOpen O → O.Nonempty → O ⊆ ((uAt r v i).X k).dom → O ⊆ closure {x | ∃ hx : x ∈ ((uAt r v i).X k).dom, MovesAt p r i v γ k k' a hm x hx} → ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k' a hm x hx := by
  first | exact @GlobalTheory.ShareOn.movesAt_of_dense | exact GlobalTheory.ShareOn.movesAt_of_dense | (intros; apply GlobalTheory.ShareOn.movesAt_of_dense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanksStatement
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistingSection_preserves_hermitianLattices_ranks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (_s : TwSec U x Z G₀) (G : WTZ E), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → GoodOn U x V dict Z G → GoodOn U x V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := by
  first | exact @GlobalTheory.FlatTw.Good.twist_goodOn | exact GlobalTheory.FlatTw.Good.twist_goodOn | (intros; apply GlobalTheory.FlatTw.Good.twist_goodOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeHermitianRankAndHostDegreeEqStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_le_hermitianRank_and_hostDegree_eq : ∀ D : D7, 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by
  first | exact @GlobalTheory.RankHostFacts.main | exact GlobalTheory.RankHostFacts.main | (intros; apply GlobalTheory.RankHostFacts.main <;> assumption)
end

