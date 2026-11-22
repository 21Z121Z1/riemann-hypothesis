import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3446
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLatticeSpanEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3185
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3441
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0090
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugedLocalHeatOperatorPowerMul
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

namespace GlobalTheory.Heat.Gauge

open GlobalTheory.KS (rsT_mul rsT_one rsT_sum rsT_sub rsT_add rsT_constFn rsT_rsT)
open GlobalTheory.HeatGlue (IsDer isDer_of_isField field_rsT ringOp_conj)

theorem op_gauged : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), (∀ a, IsField ⊤ (dd a)) → ∀ (c : R), 2 * c = 1 → ∀ (p : h₁.J × (Fin 2 → L.ι)) (k : ℕ) (O : G.left.Opens), O ≤ GlobalTheory.Heat.Gauge.W m h₁ p → ∀ (f : Γ(G.left, O)), op G dd h₁.Θ h₁.u (GlobalTheory.Heat.Gauge.gD m h₁ e p) (GlobalTheory.Heat.Gauge.gP m h₁ e c p) (GlobalTheory.Heat.Gauge.gP' m h₁ e c p) k O (rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O ^ k * f) = rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O ^ k * op G dd h₁.Θ h₁.u (h₁.d p.1) (h₁.p p.1) (h₁.p' p.1) k O f := by
  intro R _ G _ _ n X m m₁ L dd D h₁ e hdd c hc p k O hO f
  have hW1 : W m h₁ p ≤ h₁.W p.1 := heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p
  have hdF : IsField (h₁.W p.1) (h₁.d p.1) := (h₁.lift p.1).1
  have hd : IsDer (h₁.d p.1 O) := isDer_of_isField hdF (hO.trans hW1)
  have hddO : ∀ a, IsDer (dd a O) := fun a => isDer_of_isField (hdd a) le_top
  have hg : rsT (gU m h₁ e p).val O * rsT (gU m h₁ e p)⁻¹.val O = 1 := by
    rw [← rsT_mul, Units.mul_inv, rsT_one hO]
  set g := rsT (gU m h₁ e p).val O with hgdef
  set gi := rsT (gU m h₁ e p)⁻¹.val O with hgidef
  have eL : ∀ a, rsT (gL m h₁ e a p) O = dd a O g * gi := fun a => by
    rw [gL, rsT_mul, field_rsT (hdd a) le_top hO]
  have eE : rsT (gE m h₁ e p) O = h₁.d p.1 O g * gi := by
    rw [gE, rsT_mul, field_rsT hdF hW1 hO]
  have eY : ∀ a, rsT (gY m h₁ e a p) O = ∑ b, constFn G.hom O (h₁.Θ a b) * (dd b O g * gi) := fun a => by
    simp only [gY, rsT_sum, rsT_mul, rsT_constFn G.hom hO, eL]
  have eP : rsT (gP m h₁ e c p) O = rsT (h₁.p p.1) O - h₁.d p.1 O g * gi -
      constFn G.hom O c * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd a O g * gi) * (dd b O g * gi) := by
    simp only [gP, rsT_sub, rsT_mul, rsT_sum, rsT_constFn G.hom hO, eL, eE, rsT_rsT hW1 hO]
  have eDL : ∀ a b, rsT (dd a (W m h₁ p) (gL m h₁ e b p)) O = dd a O (dd b O g * gi) := fun a b => by
    rw [← field_rsT (hdd a) le_top hO, eL]
  have eP' : rsT (gP' m h₁ e c p) O = rsT (h₁.p' p.1) O +
      constFn G.hom O c * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * dd a O (dd b O g * gi) -
      ∑ a, constFn G.hom O (h₁.u a) * (dd a O g * gi) := by
    simp only [gP', rsT_sub, rsT_add, rsT_mul, rsT_sum, rsT_constFn G.hom hO, eL, eDL, rsT_rsT hW1 hO]
  have hcO : 2 * constFn G.hom O c = 1 := by
    have := congrArg (constFn G.hom O) (show c + c = 1 by linear_combination hc)
    simp only [constFn, map_add, map_one] at this ⊢
    linear_combination this
  have hs : ∀ a b, (h₁.Θ.map (constFn G.hom O)) a b = (h₁.Θ.map (constFn G.hom O)) b a := fun a b => by
    simp only [Matrix.map_apply]
    rw [show h₁.Θ a b = h₁.Θᵀ b a from rfl, h₁.symm]
  have key := ringOp_conj hd hddO hs (fun a => constFn G.hom O (h₁.u a)) (rsT (h₁.p p.1) O) (rsT (h₁.p' p.1) O) hg k f
  simp only [ringOp, Matrix.map_apply] at key
  have S1 : ∑ a, (∑ b, constFn G.hom O (h₁.Θ a b) * (dd b O g * gi)) * dd a O (g ^ k * f) =
      g ^ k * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd b O g * gi) * dd a O f +
      (k : Γ(G.left, O)) * g ^ k * f * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd a O g * gi) * (dd b O g * gi) := by
    simp only [(hddO _).pow_mul hg, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [op, gD, eY, eP, eP']
  linear_combination key + 2 * (k : Γ(G.left, O)) * S1 -
    (k : Γ(G.left, O)) * g ^ k * f * ((k : Γ(G.left, O)) *
      (∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd a O g * gi) * (dd b O g * gi)) -
      ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * dd a O (dd b O g * gi)) * hcO

end GlobalTheory.Heat.Gauge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedHeatOperatorsPreserveSectionsUpToConstantStatement
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
theorem _root_.GlobalTheory.T.glued_heat_operators_preserve_sections_up_to_constant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (n : ℕ) (dd' : Fin n → Fld t.G.left), (∀ a, IsField ⊤ (dd' a)) → ∀ (D : Derivation ℤ R R) (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) → (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) → ∀ (k : ℕ) (σ : SecM (𝟙 t.G.left) t.PP.L k) (a : R), ∃ (r : R) (σ' : SecM (𝟙 t.G.left) t.PP.L k), r ≠ 0 ∧ ∀ i, rsT (σ'.f fun _ => j i) (W i) = GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c r) * (GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c a) * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) - 2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) * rsT (σ.f fun _ => j i) (W i)) := by
  first | exact @GlobalTheory.HeatVExt.heat_section | exact GlobalTheory.HeatVExt.heat_section | (intros; apply GlobalTheory.HeatVExt.heat_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodAtOfAntitoneGapWeight
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.ShiftGood

variable {D : D7} {T : Core D} {j : ℕ}

theorem cuspW_eq_of_exZ {Y : Deep T j} {e : ℕ} {o : ℝ} (hY : Y.Good e o) {G G' : WTZ D.host.E}
    (h : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) G') : Y.V G = Y.V G' := by
  ext f
  rw [GlobalTheory.AllWt.mem_cuspW, GlobalTheory.AllWt.mem_cuspW, h]
  refine and_congr_right fun _ => forall₂_congr fun σ hσ => ?_
  rw [GlobalTheory.AllWt.modelWt_congr (Y.U σ) hσ (hY.unf σ hσ) h]

theorem goodAt_of_exZ {Y : Deep T j} {e : ℕ} {o : ℝ} (hY : Y.Good e o) {G G' : WTZ D.host.E}
    (h : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) G') (hG : Y.GoodAt G) : Y.GoodAt G' := by
  refine ⟨hasGram_nrm_of_good D T j Y e o hY G', ?_⟩
  have key : ∀ C C' : Submodule Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂), C = C' →
      ((GlobalTheory.AllWt.supLat C).FG ∧ Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.supLat C : Set C) = ⊤) →
      ((GlobalTheory.AllWt.supLat C').FG ∧ Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.supLat C' : Set C') = ⊤) := by
    rintro C _ rfl; exact id
  exact key _ _ (cuspW_eq_of_exZ hY h) hG.2

end GlobalTheory.CovTop.ShiftGood

namespace GlobalTheory.CovTop.ShiftGood

theorem goodAt_shiftG : Hypotheses2 → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : ℤ), Even n → (∀ τ, Antitone ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ)) → (∀ τ, 1 ≤ gap ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  intro hP D T hT j hp hq hf hj Y e o hY a n s hn hA hg
  obtain ⟨m, rfl⟩ := hn
  have hmul : ∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • (laOf (T.Q.Dw j) a (m + m) + s • hodgeWt (T.Q.Dw j))) 0) := by
    intro k
    refine (GlobalTheory.T.good_weight_antitone_gap hP D T hT j hp hq hf hj Y e o hY _ (fun τ => ?_) (fun τ => ?_)).1
    · intro x y hxy
      simp only [Pi.smul_apply]
      exact nsmul_le_nsmul_right (hA τ hxy) _
    · have := hg τ
      simp only [Pi.smul_apply]
      unfold gap at this ⊢
      split_ifs at this ⊢ with h1
      · simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at this ⊢
        have hk : (1 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos k
        rw [← mul_sub]
        exact this.trans (le_mul_of_one_le_left (by linarith) hk)
      · exact this
  refine goodAt_of_exZ hY ?_ ⟨hasGram_nrm_of_good D T.toCore j Y e o hY _,
    GlobalTheory.T.latW_fg_of_good hP D T hT j hp hq hf hj Y e o hY _ hA hg hmul m,
    GlobalTheory.T.weight_lattice_span_eq hP D T hT j hp hq hf hj Y e o hY _ hA hg hmul m⟩
  rw [← two_mul, GlobalTheory.CovTop.Model.exZ_shiftG]
  rfl

end GlobalTheory.CovTop.ShiftGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorFourierTermAlongFibreConnection
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
open GlobalTheory.HeatConn

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatConn
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

section T
variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem trF_term (e : ℕ) (α : Q.X) (t : Fin 4 → Q.P.L.ι) (J : (Y.H.left ⟶ Q.P.A.left) → Q.P.L.ι) (y : Y.H.left) :
    trF (fun _ : Fin 1 => Y.q.left) (fun _ => (e : ℤ)) (𝟙 _) y (fun _ => J Y.q.left) (fun _ => t 0) =
      trF (Q.famφB α) (DegPre.famε e) Y.q.left y (fun j => J (Y.q.left ≫ Q.famφB α j)) t *
        trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε (𝟙 _) y
          (fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k))) (fun k => t (![1, 2, 0, 3] k)) := by
  let G : (Y.H.left ⟶ Q.P.A.left) → Q.P.L.ι → (Y.H.left.presheaf.stalk y)ˣ := fun ψ i =>
    gm ψ y (Q.P.L.U (J ψ) ⊓ Q.P.L.U i) (Q.P.L.g (J ψ) i)
  have e1 : trF (Q.famφB α) (DegPre.famε e) Y.q.left y (fun j => J (Y.q.left ≫ Q.famφB α j)) t =
      ∏ k, G (Y.q.left ≫ Q.famφB α k) (t k) ^ DegPre.famε e k := rfl
  have e2 : trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε (𝟙 _) y
      (fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k))) (fun k => t (![1, 2, 0, 3] k)) =
      ∏ k, G (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k)) (t (![1, 2, 0, 3] k)) ^ DegPre.gtε k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.id_comp, gtφT_eq]
  have e3 : trF (fun _ : Fin 1 => Y.q.left) (fun _ => (e : ℤ)) (𝟙 _) y (fun _ => J Y.q.left) (fun _ => t 0) =
      G Y.q.left (t 0) ^ (e : ℤ) := by
    rw [trF, Fin.prod_univ_one, Category.id_comp]
  have f0 : Q.famφB α 0 = 𝟙 _ := rfl
  rw [e1, e2, e3]
  simp only [Fin.prod_univ_four, DegPre.famε, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, f0, Category.comp_id]
  rw [zpow_sub_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv, zpow_one, zpow_neg]
  abel

theorem term_germ {e : ℕ} {α : Q.X} {σ : Q.SecB e α} {τ : SecM Y.q.left Q.P.L e} (hτ : IsTerm Y e α σ τ)
    (t : Fin 4 → Q.P.L.ι) (y : Y.H.left) (h₁ : Y.q.left y ∈ LB.wchart Q.P.L (Q.famφB α) t) (h₂ : y ∈ xU Y α t) :
    gs (𝟙 _) y _ (τ.f fun _ => t 0) = gs Y.q.left y _ (σ.f t) * gs (𝟙 _) y _ (xc Y α t).val := by
  have hL : Q.P.L.IsLB := Q.P.isLB
  choose J hJ using fun χ : Y.H.left ⟶ Q.P.A.left => exists_chart hL (χ y)
  have hJ' : Good Q.P.L y J := hJ
  have e₀ := hτ Y.H (𝟙 _) y J hJ'
  have f0 : Q.famφB α 0 = 𝟙 _ := rfl
  have h₀ : y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) fun _ => t 0 := Set.mem_iInter.2 fun _ => by
    have := Set.mem_iInter.1 h₁ 0
    rw [f0] at this
    exact this
  rw [sval_of τ _ y J (fun _ => J Y.q.left) (fun _ => by simp),
    sval_of σ _ y J (fun j => J (Y.q.left ≫ Q.famφB α j)) (fun _ => by simp),
    val_of _ _ y J (fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k))) (fun k => by rw [Category.id_comp, gtφT_eq])] at e₀
  simp only [Over.id_left, Over.comp_left, Category.id_comp] at e₀
  have m₁ : (𝟙 Y.H.left : Y.H.left ⟶ Y.H.left) y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) fun _ => J Y.q.left :=
    Set.mem_iInter.2 fun _ => hJ _
  have m₂ : Y.q.left y ∈ LB.wchart Q.P.L (Q.famφB α) fun j => J (Y.q.left ≫ Q.famφB α j) :=
    Set.mem_iInter.2 fun j => hJ _
  have m₃ : (𝟙 Y.H.left : Y.H.left ⟶ Y.H.left) y ∈ LB.wchart Q.P.L (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α)
      fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k)) :=
    Set.mem_iInter.2 fun k => by
      show y ∈ (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) ⁻¹ᵁ _
      rw [gtφT_eq]; exact hJ _
  rw [sec_trans τ _ y m₁ h₀, sec_trans σ Y.q.left y m₂ h₁, gen_trans ((Y.Φ Y.H (𝟙 _)).isGen α) (𝟙 _) y m₃ h₂,
    Units.val_mul] at e₀
  rw [gs_unit (𝟙 _) y _ h₂]
  rw [trF_term Y e α t J y, Units.val_mul] at e₀
  exact ((Units.isUnit _).mul (Units.isUnit _)).mul_left_cancel (e₀.trans (mul_mul_mul_comm _ _ _ _))
end T

section T2
variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem term_germ_at {e : ℕ} {α : Q.X} {σ : Q.SecB e α} {τ : SecM Y.q.left Q.P.L e} (hτ : IsTerm Y e α σ τ)
    (t : Fin 4 → Q.P.L.ι) {Z : Scheme.{0}} (r : Z ⟶ Y.H.left) (z : Z)
    (h₁ : Y.q.left (r z) ∈ LB.wchart Q.P.L (Q.famφB α) t) (h₂ : r z ∈ xU Y α t) :
    gs r z _ (τ.f fun _ => t 0) = gs (r ≫ Y.q.left) z _ (σ.f t) * gs r z _ (xc Y α t).val := by
  have h₀ : r z ∈ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (e : ℤ)).U fun _ => t 0 :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h₁ 0
  have h₁' : Y.q.left (r z) ∈ (LB.LinComb Q.P.L (Q.famφB α) (DegPre.famε e)).U t := h₁
  have e₁ : gs Y.q.left (r z) _ (σ.f t) = gs (𝟙 _) (r z) (Y.q.left ⁻¹ᵁ _) ((Y.q.left.app _).hom (σ.f t)) := by
    rw [gs_pull (𝟙 _) Y.q.left (r z) _ h₁', Category.id_comp]
  rw [gs_stalkMap r z _ h₀, term_germ Y hτ t (r z) h₁ h₂, map_mul, ← gs_stalkMap r z _ h₂, e₁,
    ← gs_stalkMap r z _ h₁', gs_pull r Y.q.left z _ h₁']
end T2

theorem heat_term_fibre : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → ∀ (α : Q.X) (c : K), CoordEq Y h ν m₀ V pb α c → ∀ (σ σ' : Q.SecB e α), TActs Y h e α σ σ' → ∀ (i : Fin 4 → h.J) (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ Q.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) → ∀ U : A₀.left.Opens, U ≤ m₀ ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB α) (fun j => h.j (i j)) → (∀ j, U ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => h.j (i j))) U = 2 * (e : Γ(A₀.left, U)) * (rsT (ed _ (σ.f (fun j => h.j (i j)))) U + pbT m₀ (σ.f (fun j => h.j (i j))) U * (∑ j, ((DegPre.famε e j : ℤ) : Γ(A₀.left, U)) * pbT (T j) (pb (i j)) U + constFn A₀.hom U c)) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hK hD α c hC σ σ' hA i T hT₁ hT₂ U hU hUT
  obtain ⟨τ, τ', hτ, hτ', hAc⟩ := hA
  refine ext_lift Y m₀ fun Z a b w z hz => ?_
  have hV : ∀ i, V i ≤ Q.P.L.U (h.j i) := hK.2.2.1
  have hi : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j) := fun j => hUT j hz
  have ha := hF.mem_chart hD hV hT₁ w hi
  have T0 : T 0 = 𝟙 _ := hF.T_zero (hT₁ 0) (hT₂ 0)
  have wz : Y.q.left (a z) = m₀ (b z) := by
    have := congrArg (fun f => f z) w
    simpa using this
  set W := (LB.LinComb Q.P.L (Q.famφB α) (DegPre.famε e)).U fun j => h.j (i j) with hWdef
  have hU' : U ≤ m₀ ⁻¹ᵁ W := hU
  have hbW : m₀ (b z) ∈ W := hU hz
  have hqa : Y.q.left (a z) ∈ W := wz ▸ hbW
  have hb0 : (b ≫ m₀) z ∈ V (i 0) := by simpa [T0] using hi 0

  have P : ∀ j, gs b z U (pbT (T j) (pb (i j)) U) = gs (b ≫ T j) z _ (pb (i j)) := fun j =>
    gs_pbT b (T j) z (hUT j) hz _
  have Ed : gs b z U (rsT (ed W (σ.f fun j => h.j (i j))) U) = gs b z (m₀ ⁻¹ᵁ W) (ed W (σ.f fun j => h.j (i j))) :=
    gs_rsT b z hU' hz _
  have Sb : ∀ s : Q.SecB e α, gs b z U (pbT m₀ (s.f fun j => h.j (i j)) U) = gs (a ≫ Y.q.left) z W (s.f fun j => h.j (i j)) :=
    fun s => by rw [gs_pbT b m₀ z hU' hz, w]
  have Cc : gs b z U (constFn A₀.hom U c) = cst (b ≫ A₀.hom) z c := gs_constFn _ _ _ _ hz _

  have hΘ : ∀ a' b', gsH a z (h.W (i 0)) ha.1 (constFn Y.H.hom (h.W (i 0)) (h.Θ a' b')) = 0 := fun a' b' => by
    rw [← gs_eq_gsH, hF.gs_const w z (h.W (i 0)) ha.1, hF.symb, cst_eq_cstH, map_zero]
  have hop := congrArg (gsH a z (h.W (i 0)) ha.1) (hAc (i 0))
  rw [map_op h ν e hF.inv (i 0) (h.W (i 0)) le_rfl _ hΘ] at hop
  simp only [← gs_eq_gsH] at hop
  have hWc : h.W (i 0) ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (e : ℤ)).U fun _ => h.j (i 0) :=
    fun y hy => Set.mem_iInter.2 fun _ => h.le (i 0) hy
  rw [gs_rsT a z hWc ha.1, gs_rsT a z le_rfl ha.1,
    term_germ_at Y hτ' (fun j => h.j (i j)) a z hqa ha.2, ← hD.2.2 Z a b w z (i 0) hb0] at hop

  obtain ⟨δ, -, hδm, hδv⟩ := exists_stalkDer_field (isField_dE h ν hF.field (i 0)) a z ha.1
  set U' : Q.P.A.left.Opens := V (i 0) ⊓ W with hU'def
  have hqU : Y.q.left ⁻¹ᵁ U' ≤ h.W (i 0) := by
    rw [hD.1 (i 0)]; exact fun y (hy : Y.q.left y ∈ U') => hy.1
  have haV : Y.q.left (a z) ∈ V (i 0) := by
    have := ha.1; rw [hD.1 (i 0)] at this; exact this
  have haU : a z ∈ Y.q.left ⁻¹ᵁ U' := ⟨haV, hqa⟩
  have hbU : (b ≫ m₀) z ∈ U' := ⟨hb0, by simpa using hbW⟩
  have haU' : (a ≫ Y.q.left) z ∈ U' := by simpa using haU
  set f' : Γ(Q.P.A.left, U') := resG Q.P.A.left (inf_le_right : U' ≤ W) (σ.f fun j => h.j (i j)) with hf'
  have hAB : gs (𝟙 _) (a z) (h.W (i 0)) (rsT (τ.f fun _ => h.j (i 0)) (h.W (i 0))) =
      gs (𝟙 _) (a z) (Y.q.left ⁻¹ᵁ U') ((Y.q.left.app U').hom f') *
        gs (𝟙 _) (a z) (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))
          (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))) := by
    rw [gs_rsT (𝟙 _) (a z) hWc ha.1, term_germ Y hτ (fun j => h.j (i j)) (a z) hqa ha.2,
      gs_rsT (𝟙 _) (a z) inf_le_right ha, gs_pull (𝟙 _) Y.q.left (a z) U' haU, Category.id_comp, hf',
      gs_res Y.q.left (a z) inf_le_right haU]
  have hδ := hδv (h.W (i 0)) le_rfl ha.1 (rsT (τ.f fun _ => h.j (i 0)) (h.W (i 0)))
  rw [hAB, hδm, hδv _ hqU haU, hδv _ inf_le_left ha, ← hD.2.1 Z a b w z (i 0) U' inf_le_left hbU,
    hf', hK.1.res W U' inf_le_right le_top, gs_rsT b z (fun y (hy : m₀ y ∈ U') => hy.2) hbU,
    hC T hT₁ hT₂ Z a b w z i hi, ← gs_stalkMap a z _ haU, ← gs_stalkMap a z _ ha, gs_pull a Y.q.left z U' haU,
    gs_res _ z inf_le_right haU', gs_rsT a z inf_le_right ha] at hδ
  rw [gs_rsT a z hWc ha.1 (τ.f fun _ => h.j (i 0)), term_germ_at Y hτ (fun j => h.j (i j)) a z hqa ha.2, ← hδ] at hop
  have hX : IsUnit (gs a z (xU Y α fun j => h.j (i j)) (xc Y α fun j => h.j (i j)).val) := by
    rw [gs_unit a z _ ha.2]; exact Units.isUnit _
  rw [Sb σ', gs_eq_gsH b z U hz]
  simp only [map_mul, map_add, map_sum, map_natCast, map_ofNat, map_intCast]
  simp only [← gs_eq_gsH b z U hz]
  rw [Ed, Sb σ, Cc, Fin.sum_univ_four, P 0, P 1, P 2, P 3]
  rw [T0, Category.comp_id] at hop ⊢
  simp only [W] at hop ⊢
  have f0 : DegPre.famε e 0 = (e : ℤ) - 1 := rfl
  have f1 : DegPre.famε e 1 = 1 := rfl
  have f2 : DegPre.famε e 2 = -1 := rfl
  have f3 : DegPre.famε e 3 = 1 := rfl
  rw [f0, f1, f2, f3]
  push_cast
  apply hX.mul_left_cancel
  linear_combination hop
end GlobalTheory.HeatConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorFourierTermValuesEqOfLocalIdentityStatement
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
theorem _root_.GlobalTheory.T.heat_operator_fourier_term_values_eq_of_local_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → ∀ c : ℕ → Q.X → R, (∀ (i : h.J) (i' : h'.J) (k : ℕ) (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i ⊓ h'.W i' → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (Y.q.left ⁻¹ᵁ V) (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * f) = pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * (op Y.H dd h'.Θ h'.u (h'.d i') (h'.p i') (h'.p' i') k (Y.q.left ⁻¹ᵁ V) f + constFn Y.H.hom _ (c k α) * f)) → ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (c k α)) * sval σ x.left z J := by
  first | exact @GlobalTheory.Heat.sval_eq_of_localIdentity | exact GlobalTheory.Heat.sval_eq_of_localIdentity | (intros; apply GlobalTheory.Heat.sval_eq_of_localIdentity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatSymbolRegularOnSectionNonvanishingLocusStatement
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
theorem _root_.GlobalTheory.T.heat_symbol_regular_on_section_nonvanishing_locus : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → ∀ (k : ℕ), 1 ≤ k → ∀ s : SecM (𝟙 P₀.A.left) P₀.L k, ⊤ ≤ ξ ⁻¹ᵁ (Out.nonzeroLocus s) → (∀ f f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ h : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ h = ∑ a, ∑ e, Λ a e * δ a (valR ξ _ f) * δ e (valR ξ _ f')) ∧ (∀ f : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, Λ a e * (δ a (valR ξ _ (s.f fun _ => j₀)) / valR ξ _ (s.f fun _ => j₀)) * δ e (valR ξ _ f)) := by
  first | exact @GlobalTheory.HeatLoc.symb_regular | exact GlobalTheory.HeatLoc.symb_regular | (intros; apply GlobalTheory.HeatLoc.symb_regular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePullbackGenOfFrameIsGen
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

variable {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
  {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ}

theorem pulled_back_lineBundle_transition_unit_eq_restriction {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j j' : PUnit.{1} → L.ι) :
    (L.pull f).g j j' = res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => f) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ => f) j' PUnit.unit)))
      (pullU f _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
  have e : ∀ u : Γ(Y, L.wchart (fun _ => f) j ⊓ L.wchart (fun _ => f) j')ˣ, (∏ _k : PUnit.{1}, u ^ (1 : ℤ)) = u :=
    fun u => by simp
  exact e _

theorem pull_g_eq (h : IsGrpPullback H G x ψ) (j j' : ((hodge G g).pull x).ι) :
    ((hodge G g).pull x).g j j' =
      (isFrame_chart h j).detUnit (isFrame_chart h j') inf_le_left inf_le_right := by
  have e₁ := IsFrame.detUnit_map_iso
    (GlobalTheory.BadPt.Fibre.frame_pb x (j PUnit.unit).isFrame (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit))
    (GlobalTheory.BadPt.Fibre.frame_pb x (j' PUnit.unit).isFrame (LB.wchart_le (hodge G g) (fun _ => x) j' PUnit.unit))
    (omegaBase h) (inf_le_left : LB.wchart (hodge G g) (fun _ => x) j ⊓ LB.wchart (hodge G g) (fun _ => x) j' ≤ _)
    inf_le_right
  refine Eq.trans ?_ e₁.symm
  have hT : LB.wchart (hodge G g) (fun _ => x) j ⊓ LB.wchart (hodge G g) (fun _ => x) j' ≤
      x ⁻¹ᵁ ((j PUnit.unit).U ⊓ (j' PUnit.unit).U) :=
    le_inf (inf_le_left.trans (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le (hodge G g) (fun _ => x) j' PUnit.unit))
  refine Eq.trans ?_ (GlobalTheory.Vert.DivPull.detUnit_congr _ _ ((j PUnit.unit).isFrame.pullback x)
    ((j' PUnit.unit).isFrame.pullback x) _ _ (hT.trans (x.preimage_mono inf_le_left))
    (hT.trans (x.preimage_mono inf_le_right))
    (fun i => (QCoh.res_pullbackSections _ _ _ _ _).trans (QCoh.res_pullbackSections _ _ _ _ _).symm)
    (fun i => (QCoh.res_pullbackSections _ _ _ _ _).trans (QCoh.res_pullbackSections _ _ _ _ _).symm)).symm
  refine Units.ext ?_
  refine (congrArg Units.val (pulled_back_lineBundle_transition_unit_eq_restriction (hodge G g) x j j')).trans (Eq.trans ?_
    (IsFrame.val_detUnit_pullback (j PUnit.unit).isFrame (j' PUnit.unit).isFrame x inf_le_left inf_le_right hT).symm)
  rfl

theorem gen_isGen : ∀ {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a), (gen h ha).IsGen := by
  intro S' T G _ H _ x ψ _ g h a ha j j'
  refine (IsFrame.res_detUnit _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (pull_g_eq h j j').symm (IsFrame.res_detUnit _ _ _ _ _).symm)
  exact (IsFrame.detUnit_mul _ _ _ _ _ _).symm

end GlobalTheory.HodgeFrameGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealEqSpanMonomialOfOrdersAlongCompleteDVRStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_eq_span_monomial_of_orders_along_completeDVR : ∀ (k : Type) [Field k] [CharZero k] (m e : ℕ) (I : Ideal (ChartRing k m e)) (a : Fin m → ℕ), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ψ : ChartRing k m e →+* W, Function.Injective ψ → IsLocalHom ψ → I.map ψ = Ideal.span {ψ (∏ i, bdParam k m e i ^ a i)}) → I = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
  first | exact @GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr | exact GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr | (intros; apply GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageIsoUniformisedFactorOfAdjointPairStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_image_iso_uniformised_factor_with_adjoint_pair : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ (ε : G ≅ G₀) (u : G' ⟶ G₀) (u' : G₀ ⟶ G'), IsMonHom ε.hom ∧ IsMonHom u ∧ IsMonHom u' ∧ ε.hom = inc ≫ u ∧ u ≫ u' = oG.act (Star.star F.e * F.f * F.e) ∧ GAdj U'.LG.L U₀.LG.L u u' := by
  first | exact @GlobalTheory.MumIsoAdj.iso_of_factor_adj | exact GlobalTheory.MumIsoAdj.iso_of_factor_adj | (intros; apply GlobalTheory.MumIsoAdj.iso_of_factor_adj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastBis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem USetup.range_π_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (η : Xo.XF c) (A : Set C.Z), (∀ w, X₁.uΩ w = η) → closure {C.i η} = A → Set.range X₁.π = A := by
  intro E _ _ _ H Dw _ l Xo c C X₁ η A hη hA
  haveI := X₁.fin
  have hc : IsClosedMap X₁.π.base := X₁.π.isClosedMap
  let w₀ : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
  have hgen : X₁.M.pt w₀ = genericPoint X₁.M.Z := X₁.M.pt_apply w₀
  have hpt : X₁.π (X₁.M.pt w₀) = C.i η := by
    have h := congrArg (fun f => f.base w₀) X₁.comp
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hη w₀]
    simpa using h
  have huniv : closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) = Set.univ := genericPoint_spec X₁.M.Z
  rw [← hA, ← hpt, hgen, ← Set.image_singleton, ← Set.image_univ, ← huniv]
  exact (hc.closure_image_eq_of_continuous X₁.π.continuous _).symm

end GlobalTheory.UPoinc
end

