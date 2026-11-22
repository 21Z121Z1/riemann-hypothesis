import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0081
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2257
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeWchart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanGauge

def trV {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι) (n : ℤ) : A :=
  valR y (L.U a ⊓ L.U b) ((L.g a b) ^ n).val

def pickJ {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) (i : Fin 4) : Ix :=
  jf (Classical.epsilon fun i' => φs i' = φs i)

theorem pickJ_congr {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) {i₁ i₂ : Fin 4}
    (h : φs i₁ = φs i₂) : pickJ φs jf i₁ = pickJ φs jf i₂ := by
  unfold pickJ; rw [h]

theorem pickJ_spec {X Y : Scheme.{0}} {Ix : Type} (φs : Fin 4 → (Y ⟶ X)) (jf : Fin 4 → Ix) (i : Fin 4) :
    ∃ i', φs i' = φs i ∧ pickJ φs jf i = jf i' :=
  ⟨_, Classical.epsilon_spec (p := fun i' => φs i' = φs i) ⟨i, rfl⟩, rfl⟩

theorem trV_add {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n m : ℤ) : trV L y a b n * trV L y a b m = trV L y a b (n + m) := by
  unfold trV
  rw [zpow_add, Units.val_mul, GlobalTheory.ZH.CrdCalc.valR_mul y _ h]

theorem isUnit_trV {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n : ℤ) : IsUnit (trV L y a b n) := by
  unfold trV
  rw [GlobalTheory.ZH.CrdCalc.valR_eq y _ h]
  exact (Units.isUnit _).map _

theorem top_le_wchart {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (h : ∀ k, ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ L.U (j k)) : ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j :=
  fun q _ => Set.mem_iInter.2 fun k => h k (x := q) trivial

theorem wchart_top_le {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j) (k : K) : ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ L.U (j k) :=
  fun q _ => Set.mem_iInter.1 (h (x := q) trivial) k

theorem trV_zero {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) : trV L y a b 0 = 1 := by
  unfold trV
  rw [zpow_zero, Units.val_one, GlobalTheory.ZH.CrdCalc.valR_eq y _ h, map_one]

theorem trV_pow {X : Scheme.{0}} (L : LB X) {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b)) (n : ℤ) (m : ℕ) : trV L y a b n ^ m = trV L y a b (n * m) := by
  unfold trV
  rw [GlobalTheory.ZH.CrdCalc.valR_eq y _ h, GlobalTheory.ZH.CrdCalc.valR_eq y _ h, ← map_pow, ← Units.val_pow_eq_pow_val, ← zpow_natCast,
    ← zpow_mul]

end GlobalTheory.MBLow.TanGauge

namespace GlobalTheory.MBLow.TanGauge

theorem gl_corr : ∀ {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')),
    LB.Gen.Corr L φ ε φ' ε' t t' → ∀ (j : K → L.ι) (j' : K' → L.ι), LB.Coh L φ j → LB.Coh L φ' j' →
    (∀ k k', φ k = φ' k' → j k = j' k') → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ' j' →
    valR y (LB.wchart L φ j) (t.s j).val = valR y (LB.wchart L φ' j') (t'.s j').val := by
  intro X Y L K K' _ _ φ ε φ' ε' t t' hc j j' hj hj' hx A _ y h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') := fun q hq => ⟨h hq, h' hq⟩
  have e := congrArg Units.val (hc j j' hj hj' hx)
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ j) hh (t.s j).val
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ' j') hh (t'.s j').val
  refine e1.symm.trans (Eq.trans ?_ e2)
  exact congrArg (valR y _) e

theorem gl_pullGen : ∀ {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (j : K → L.ι) {A : Type} [CommRing A] (y : Sp A ⟶ Z),
    ⊤ ≤ (y ≫ h) ⁻¹ᵁ LB.wchart L φ j →
    valR y (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε c h).s j).val = valR (y ≫ h) (LB.wchart L φ j) (c.s j).val := by
  intro X Y Z L K _ φ ε c h j A _ y hy
  have hy' : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j :=
    top_le_wchart L _ _ _ fun k => by rw [← Category.assoc]; exact wchart_top_le L _ _ _ hy k
  have e := GlobalTheory.ZH.CrdCalc.valR_res y ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
    LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j) hy' (pullU h _ (c.s j)).val
  refine e.trans ?_
  exact GlobalTheory.ZH.EvCrd.valR_comp y h (LB.wchart L φ j) (fun q hq => hy hq) _

theorem gl_gtφT_pull : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T T' : Over (Sp R)) (h : T'.left ⟶ T.left),
    h ≫ T.hom = T'.hom → ∀ (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A), b'.left = h ≫ b.left → ∀ (α : D.X) (i : Fin 4),
    DegPre.gtφT D T' b' α i = h ≫ DegPre.gtφT D T b α i := by
  intro R _ _ D T T' h hh b b' hb α i
  have hb' : b' = Over.homMk h hh ≫ b := by
    ext; simpa using hb
  subst hb'
  fin_cases i
  · change (padd D.P.A (DegPre.cT D T' α) (Over.homMk h hh ≫ b)).left = (Over.homMk h hh : T' ⟶ T).left ≫
      (padd D.P.A (DegPre.cT D T α) b).left
    rw [← Over.comp_left]; congr 1; simp [padd, comp_lift_assoc, DegPre.cT]
  · change (toUnit T' ≫ D.c α).left = (Over.homMk h hh : T' ⟶ T).left ≫ (toUnit T ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · show (Over.homMk h hh ≫ b).left = h ≫ b.left
    simp
  · change (toUnit T' ≫ η[D.P.A]).left = (Over.homMk h hh : T' ⟶ T).left ≫ (toUnit T ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp

theorem gl_gtφT_famφB : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Sp R)) (b : T ⟶ D.P.A) (α : D.X) (i : Fin 4),
    DegPre.gtφT D T b α i = b.left ≫ D.famφB α (![1, 2, 0, 3] i) := by
  intro R _ _ D T b α i
  have pc : ∀ (x y : T ⟶ D.P.A), padd D.P.A x y = padd D.P.A y x := fun x y => by
    show x * y = y * x
    exact mul_comm x y
  fin_cases i
  · change (padd D.P.A (DegPre.cT D T α) b).left = b.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left, pc]; congr 1; simp [padd, comp_lift_assoc, DegPre.cT]
  · change (toUnit T ≫ D.c α).left = b.left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · exact (Category.comp_id _).symm
  · change (toUnit T ≫ η[D.P.A]).left = b.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp

theorem gl_prB : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (α : D.X) (i : Fin 4),
    DegPre.famφ D C α i = (DegPre.prB D C).left ≫ D.famφB α i := by
  intro R _ _ D C _ _ α i
  fin_cases i
  · exact (Category.comp_id _).symm
  · change (padd D.P.A (DegPre.prB D C) (toUnit _ ≫ D.c α)).left =
      (DegPre.prB D C).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left]; congr 1; simp [padd, comp_lift_assoc]
  · change (toUnit _ ≫ D.c α).left = (DegPre.prB D C).left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · change (toUnit _ ≫ η[D.P.A]).left = (DegPre.prB D C).left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp

theorem gl_prB' : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (b : TE R C ⟶ D.P.A),
    (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ≫ (DegPre.prB D C).left =
      b.left := by
  intro R _ _ D C _ _ b
  rw [← Over.comp_left, lift_snd]

theorem gl_famφ : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (b : TE R C ⟶ D.P.A) (α : D.X) (i : Fin 4),
    (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ≫ DegPre.famφ D C α i =
      b.left ≫ D.famφB α i := by
  intro R _ _ D C _ _ b α i
  rw [gl_prB D C α i, ← Category.assoc, gl_prB' D C b]

theorem gl_scal : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (b : TE R C ⟶ D.P.A) (c : C),
    valR (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ⊤
      (scal (fst (TF (R := R) C) D.P.A).left c) = TrivSqZeroExt.inl c := by
  intro R _ _ D C _ _ b c
  have hq : (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) b).left ≫
      (fst (TF (R := R) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h := GlobalTheory.ZH.FormCount.valR_scal (algebraMap C (DualNumber C)) _ _ hq ⊤ (fun _ _ => trivial) c
  have e : resTop ⊤ (scal (fst (TF (R := R) C) D.P.A).left c) = scal (fst (TF (R := R) C) D.P.A).left c := by
    simp [resTop]
  rw [e] at h
  rw [h, TrivSqZeroExt.algebraMap_eq_inl]

theorem gl_tan : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (gm₀ : GtPt D (epsR R)), GtTan gm₀ →
    redE R ≫ gm₀.b.left = eSec D.P.A := by
  intro R _ _ D gm₀ hT
  obtain ⟨o, ⟨hb, -⟩, h1, -⟩ := hT
  rw [← h1, hb]
  have hw := Over.w (toUnit (baseOver (Sp R)))
  have e : (toUnit (baseOver (Sp R))).left = 𝟙 _ := by simpa using hw
  simp only [DegPre.zeroT, Over.comp_left, e, Category.id_comp]
  rfl

theorem gl_TF : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    (TF (R := R) C).hom = spMap (toF R C) := by
  intro R _ _ C _ _
  simp only [TF, jFK, jK, Over.mk_hom, spMap, toF, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem gl_redE : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    redE C ≫ spMap (dualMap (toF R C)) = spMap (toF R C) ≫ redE R := by
  intro R _ _ C _ _
  simp only [redE, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun z => ?_
  simp [dualMap, toF]

theorem gl_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [Field C] [Algebra (FractionRing R) C],
    spMap (dualMap (toF R C)) ≫ (epsR R).hom = (TE R C).hom := by
  intro R _ _ C _ _
  simp only [TE, epsR, Over.mk_hom, gl_TF, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun z => ?_
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, toF, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.MBLow.TanGauge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionNefLeCuspFormGrowthStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topSelfIntersection_nef_le_cuspFormGrowth : GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (u : AllWt.Weight Dw), IsVariety₀ X Z → 1 ≤ dimFlag Dw → (∀ la, CuspIso X Z U la) → (∃ f : Cusp Z U u, f ≠ 0) → letI := algebraΓOfHom (str₀ X Z); IsNef c.F (L₀ X Z u) → ENNReal.ofReal (topSelfIntersection c.F (L₀ X Z u) (dimFlag Dw) : ℝ) ≤ GlobalTheory.CompHt.growthOn U Z (wtOf Dw u 0) := by
  first | exact @GlobalTheory.NefCuspGrowth.topSelf_le_growthOn | exact GlobalTheory.NefCuspGrowth.topSelf_le_growthOn | (intros; apply GlobalTheory.NefCuspGrowth.topSelf_le_growthOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureEqOfIsAlgebraicResidueStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_closure_eq_of_isAlgebraic_residue : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) [LocallyOfFiniteType sX] [LocallyOfFiniteType (π ≫ sX)] (y : Y), (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) → topologicalKrullDim (closure {y} : Set Y) = topologicalKrullDim (closure {π y} : Set X) := by
  first | exact @GlobalTheory.ClosureDim.dim_closure_eq_of_isAlgebraic | exact GlobalTheory.ClosureDim.dim_closure_eq_of_isAlgebraic | (intros; apply GlobalTheory.ClosureDim.dim_closure_eq_of_isAlgebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFamilyEstimateStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_ratio_family_estimate : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → FieldDat → TorEx → (Lf (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) := by
  first | exact @GlobalTheory.ThmAUpper.thmA_upper | exact GlobalTheory.ThmAUpper.thmA_upper | (intros; apply GlobalTheory.ThmAUpper.thmA_upper <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSymplecticLabelsOfLevelStructureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionSymplecticLabels_of_levelStructure : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (g k : ℕ), 1 ≤ k → ∀ (ζ : Cˣ) (pt : (Fin (2 * g) → ZMod k) → (TFK (R := V) C ⟶ A.A)), IsPrimitiveRoot ζ k → (∀ a b, pt (a + b) = pt a * pt b) → Function.Injective pt → (∀ z : TFK (R := V) C ⟶ A.A, z ^ k = 1 → ∃ a, pt a = z) → (∀ i j, WeilIs A.A A.L k (pt (Pi.single i 1)) (pt (Pi.single j 1)) (unitOn (ζ ^ stdSymp g i j))) → ∃ (p : (Fin (2 * g) → ZMod k) → QkPt D.toPre C k) (q : (Fin (2 * g) → ZMod k) → N.QT k), QLevel N g k ζ q ∧ ∀ a, ν.QPt (p a) (q a) ∧ QkToAkU U.toUnifPre C k (p a) (pt a) := by
  first | exact @GlobalTheory.MBLow.qLevel_of_torsion_labels | exact GlobalTheory.MBLow.qLevel_of_torsion_labels | (intros; apply GlobalTheory.MBLow.qLevel_of_torsion_labels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtDualNumberTermValueSmulStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtDualNumberTermValue_smul : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (a : F) (gm : GtPt D (TE R F)) (α : N.X),
    jc ν (a • s) gm α = TrivSqZeroExt.inl a * jc ν s gm α := by
  first | exact @GlobalTheory.JcSmul.jc_smul | exact GlobalTheory.JcSmul.jc_smul | (intros; apply GlobalTheory.JcSmul.jc_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionCharacterValueConstantTermOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_characterValue_constantTerm_one : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → ∀ (χ : D.X),
    (vE (gm.s χ) (𝟙 _) ν.J).fst = 1 := by
  first | exact @GlobalTheory.MBLow.Cl.fst_vE_eq_one | exact GlobalTheory.MBLow.Cl.fst_vE_eq_one | (intros; apply GlobalTheory.MBLow.Cl.fst_vE_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionDualCharValuesMulCubeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_dualCharValues_mul_cube : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)) (χ χ' : D.X),
    vE (gm.s (χ + χ')) (𝟙 _) ν.J *
        vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      vE (gm.s χ) (𝟙 _) ν.J * vE (gm.s χ') (𝟙 _) ν.J := by
  first | exact @GlobalTheory.DualMult.mult_vE | exact GlobalTheory.DualMult.mult_vE | (intros; apply GlobalTheory.DualMult.mult_vE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentCharacterValuesAdditive
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.GtTanClass

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem exists_unit {T : Over (Sp R)} (g : GtPt D T) (hb : g.b = 1) (χ : D.X) :
    ∃ ρ : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ T.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → val (g.s χ) q z J = Geo.Tor.gm q z ⊤ ρ := by
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T g.b χ) (ε' := DegPre.gtε)
    (fun U _ h => Eq.symm (by
      refine (prod_pt g.b χ h).trans ?_
      rw [hb, _root_.mul_one]; simp)) (LB.oneGen D.P.L (Y := T.left))
    (fun i j => (map_one _).trans
      ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  obtain ⟨ρ, hρ⟩ := Geo.Tor.exists_ratio D.P.isLB rfl (g.s χ) u (g.isGen χ) hu
  exact ⟨ρ, fun Z q z J hJ => by rw [hρ Z q z J hJ, vu Z q z J hJ, val_one, _root_.mul_one]⟩

omit [IsDomain R] in
theorem gs_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (z : Sp B) (a : A) :
    gs (spMap f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = toStkA z (f a) := by
  rw [gs_eq _ _ ⊤ trivial]
  have e := congrArg (fun k => k.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact congrArg ((Sp B).presheaf.germ ⊤ z trivial).hom e.symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (gm : GtPt D (epsR R)), GtTan gm → gm.b = DegPre.zeroT D (epsR R) → ∃ l : D.X →+ R, ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  intro R _ _ _ D gm ⟨o, ho, hp⟩ hb
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] using
      IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hb1 : gm.b = 1 := hb
  choose ρ hρ using exists_unit gm hb1
  choose u hu using fun χ =>
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).commRingCatIsoToRingEquiv.symm.surjective (ρ χ).val
  have hv : ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → (val (gm.s χ) q z J).val =
        gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (u χ)) := fun χ Z q z J hJ =>
    (congrArg Units.val (hρ χ Z q z J hJ)).trans ((gs_unit q z ⊤ trivial _).symm.trans
      (congrArg (gs q z ⊤) (hu χ).symm))
  have h1 : ∀ χ, TrivSqZeroExt.fst (u χ : DualNumber R) = 1 := fun χ => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt R)
    have e : val (gm.s χ) (redE R) (cpt R) J = 1 := by
      have e₁ := (val_corr hJ (hp.2 χ) (𝟙 (Sp R))).trans (val_pull hJ _ _ _)
      have e₂ := (val_corr hJ (ho.2 χ) (𝟙 (Sp R))).trans (val_one _)
      rw [← e₂, e₁]
      congr 1
    have e' := hv χ _ (redE R) (cpt R) J hJ
    rw [e] at e'
    refine toStkA_injective (A := R) ?_
    rw [map_one]
    exact (gs_spMap (TrivSqZeroExt.fstHom R R R).toRingHom (cpt R) (u χ)).symm.trans e'.symm
  have hm : ∀ χ χ', (u (χ + χ') : DualNumber R) = u χ * u χ' := fun χ χ' => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt (DualNumber R))
    have C : IsCub (th D (T := epsR R) (cpt (DualNumber R)) J) := isCub_cubV D.cub hJ
    have e := cv_add gm hJ χ χ'
    rw [hb1, C.face₃, _root_.mul_one] at e
    have k : ∀ χ, (cv gm χ (cpt (DualNumber R)) J).val = toStkA (cpt (DualNumber R)) (u χ) := fun χ =>
      (hv χ _ (𝟙 _) _ J hJ).trans (gs_eq _ _ ⊤ trivial _)
    refine toStkA_injective (A := DualNumber R) ?_
    rw [map_mul]
    exact (k _).symm.trans ((congrArg Units.val e).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) (k _) (k _))))
  refine ⟨AddMonoidHom.mk' (fun χ => TrivSqZeroExt.snd (u χ : DualNumber R)) fun χ χ' => ?_, fun χ Z q z J hJ => ?_⟩
  · rw [hm, DualNumber.snd_mul, h1, h1]; ring
  · refine (hv χ Z q z J hJ).trans (congrArg (fun x => gs q z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom x)) ?_)
    exact TrivSqZeroExt.ext (by simp [h1]) (by simp)

end GlobalTheory.MBLow.GtTanClass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSeesawDictionaryTripleConditionsStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerStage_seesawDictionary_tripleConditions : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ), ∀ t : T,
      GlobalTheory.SquareComm.IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧
      (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧
        HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧
      GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧
      (∀ P g h, thetaKO (X.ω t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧
      ∀ P g h, thetaKO (X.ω' t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  first | exact @GlobalTheory.StageDict.dictionary_at_stage | exact GlobalTheory.StageDict.dictionary_at_stage | (intros; apply GlobalTheory.StageDict.dictionary_at_stage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHeckeLevelVectorsEqDimMulLocalTracesStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_hecke_levelVectors_eq_dim_mul_local_traces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n), (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) = dimW lam * ∏ᶠ w ∈ S, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id := by
  first | exact @GlobalTheory.BCT.trOn_hop_eq_dimW_mul_finprod_twTr | exact GlobalTheory.BCT.trOn_hop_eq_dimW_mul_finprod_twTr | (intros; apply GlobalTheory.BCT.trOn_hop_eq_dimW_mul_finprod_twTr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitGenericPointMemCompactFlagSpaceOpenPartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitGenericPoint_mem_compactFlagSpaceOpenPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (y : Y₀ TF.X Z) (K : Type) [Field K] (g : (Y₀ TF.X Z).presheaf.stalk y →+* K), Function.Injective g → ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) ⁻¹ᵁ flagOpen TF.X := by
  first | exact @GlobalTheory.GenTrait.top_le_preimage_flagOpen | exact GlobalTheory.GenTrait.top_le_preimage_flagOpen | (intros; apply GlobalTheory.GenTrait.top_le_preimage_flagOpen <;> assumption)
end

