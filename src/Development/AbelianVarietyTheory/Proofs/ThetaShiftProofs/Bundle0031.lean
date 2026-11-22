import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstPtsAddSmul
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts
open ConstGrp

theorem constPts_add_smul : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , (∀ v v', Ξ.x (v + v') = Ξ.x v * Ξ.x v') ∧ ∀ (e : 𝓞 E) v, Ξ.x (Λ.A.actV e v) = Ξ.x v ≫ W.t.act.act e := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ
  obtain ⟨hadd, -, hact⟩ := GlobalTheory.T.analyticDictionaryExp_additive_surjective_linear hL hL2 E H D l c O β b a Λ
  have hG := hL.globalFns
  obtain ⟨gp, hw, -, ho, -, -⟩ := W.spec
  have hw' := (isGen_iff _).1 hw
  have hb : ∀ v, (Ξ.g v).b.left ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.ex0 v).b.left :=
    fun v => (Ξ.g_rel v 0).1 2
  let ρ : Over.mk (selfR.hom ≫ spMap (PowerSeries.C (R := ℂ))) ⟶ Out.TF (R := ℂ) ℂ :=
    Over.homMk (spMap (PowerSeries.C (R := ℂ))) (by
      rw [← Over.w (Λ.ex0 0).b]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (hb 0).symm).trans ?_)
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) gp.1.w).trans ?_)
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (Ξ.g 0).b)))
  have r : ∀ v, Rel gp W.w W.e ρ (Ξ.g v) (Λ.ex0 v) := fun v =>
    rel_of_pmaps (fun x => (Ξ.g_rel v x).1) fun x =>
      pmaps_of_genRelR hw' W.P.D.toPre.P.isLB a.D₀.P.isLB ((Ξ.g v).isGen _)
        (DVR.pullGen_isGen _ _ _ _ ((Λ.ex0 v).isGen x) _) (Ξ.g_rel v x)
  have hc : ∀ x, pushHom gp selfR (DVR.cP W.P.D.toPre selfR (W.e x)) = ρ ≫ DVR.cP a.D₀ _ x := fun x =>
    Over.OverMorphism.ext ((Ξ.g_rel 0 x).1 1)
  have : IsHausdorff ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
    infer_instance
  refine ⟨fun v v' => (Ξ.x_pt (v + v')).unique (((Ξ.x_pt v).mul hG (Ξ.x_pt v')
    (isAdd_of_rel hG hw' hc W.e.surjective (r v) (r v') (r (v + v')) (hadd v v')))), fun e v => ?_⟩
  have hs := hact e v
  clear hact hadd
  have r₁ := r v
  have r₂ := r (Λ.A.actV e v)
  have x₁ := Ξ.x_pt v
  have x₂ := Ξ.x_pt (Λ.A.actV e v)
  letI := H.starRing
  exact x₂.unique (x₁.smul hG W.P.lin e
    (isSmulPt_of_rel hG hw' hc W.e.surjective W.P.oD a.oa (fun s x => W.e.map_smul s x) ho e r₁ r₂ hs))

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantSectionMulCoordDualNumberPoint
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanAlg

open ConstTerm

theorem core {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    {R₀ : Type} [CommRing R₀] [IsDomain R₀] {D₀ : Out.DegPre R₀} {S₀ : Type} [CommRing S₀] {σ₀ : Sp S₀ ⟶ Sp R₀}
    (κ : R →+* S) (ρ : S₀ →+* S) {φ : D.toPre.P.A.left ⟶ D₀.P.A.left}
    (w : LB.Iso D.toPre.P.L (D₀.P.L.pull φ)) (g : Out.GtPt D.toPre (Over.mk (spMap κ)))
    (g₀ : Out.GtPt D₀ (Over.mk σ₀)) {α : D.toPre.X} {α₀ : D₀.X}
    (hg : GenRelR (A := S) w (g.s α) (LB.pullGen _ _ _ (g₀.s α₀) (spMap ρ))) {j : ℕ} (s₀ : D₀.SecB j α₀)
    (f : D.toPre.SecB j α) (r : R)
    (hf : ∀ (p : Sp S ⟶ D.toPre.P.A.left) (jf : Fin 4 → D.toPre.P.L.ι) (j₀ : Fin 4 → D₀.P.L.ι),
      p ≫ D.toPre.P.A.hom = spMap κ →
      (∀ i, ⊤ ≤ (p ≫ D.toPre.famφB α i) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
      ∃ t : Fin 4 → Sˣ, (∀ i, (t i : S) = valR (p ≫ D.toPre.famφB α i) _ (w.s (fun _ => j₀ i, jf i)).val) ∧
        (∏ i, t i ^ Out.DegPre.famε j i : Sˣ) * valR p (LB.wchart D.toPre.P.L (D.toPre.famφB α) jf) (f.f jf) =
          κ r * valR (p ≫ φ) (LB.wchart D₀.P.L (D₀.famφB α₀) j₀) (s₀.f j₀))
    (jM : D.toPre.P.L.ι) (jf jt : Fin 4 → D.toPre.P.L.ι) (k : Fin 4 → D₀.P.L.ι)
    (hj : FormalValue.CohCharts g α jM jf jt)
    (cg : ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀) k) :
    valR (A := S) g.b.left _ (w.s (fun _ => k 2, jM)).val ^ j *
        (FormalValue.famVal g f jf * FormalValue.coordVal g α jt) =
      κ r * ρ (valR (A := S₀) g₀.b.left (LB.wchart D₀.P.L (D₀.famφB α₀) ![k 2, k 0, k 1, k 3])
        (s₀.f ![k 2, k 0, k 1, k 3]) *
        valR (A := S₀) (𝟙 _) (LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀) k) ((g₀.s α₀).s k).val) := by
  have hφ : ∀ i, FormalValue.coordφ g α i ≫ φ =
      spMap ρ ≫ (show Sp S₀ ⟶ _ from Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀ i) := hg.1
  have hq : ∀ i, FormalValue.basePt g ≫ D.toPre.famφB α i = FormalValue.coordφ g α (![2, 0, 1, 3] i) :=
    comp_famφB D.toPre g.b α
  have hq₀ := comp_famφB D₀ g₀.b α₀
  have ejf : ∀ i, jf i = jt (![2, 0, 1, 3] i) := fun i => hj.2.2 (.inr (.inl i)) (.inr (.inr _)) (hq i)
  have ejM : jM = jt 2 := hj.2.2 (.inl PUnit.unit) (.inr (.inr 2)) rfl
  have hk : ∀ i, ⊤ ≤ (show Sp S₀ ⟶ _ from Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀ i) ⁻¹ᵁ D₀.P.L.U (k i) :=
    fun i => cg.trans (LB.wchart_le _ _ _ i)
  have ek : ![k 2, k 0, k 1, k 3] = fun i => k (![2, 0, 1, 3] i) := by
    funext i; fin_cases i <;> rfl
  rw [ek]
  subst ejM
  obtain rfl : jf = fun i => jt (![2, 0, 1, 3] i) := funext ejf
  have hd : ∀ i, ⊤ ≤ FormalValue.coordφ g α i ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => k i, jt i) :=
    fun i => le_div _ (hφ i ▸ FormalValue.top_le_comp (hk i) _) (hj.2.1.trans (LB.wchart_le _ _ _ i))
  obtain ⟨t, ht, e₁⟩ := hf (FormalValue.basePt g) (fun i => jt (![2, 0, 1, 3] i)) (fun i => k (![2, 0, 1, 3] i))
    (Over.w g.b) (fun i => by rw [hq i]; exact hd _)
  simp only [hq] at ht
  have cf : ⊤ ≤ (show Sp S₀ ⟶ _ from g₀.b.left) ⁻¹ᵁ D₀.P.L.wchart (D₀.famφB α₀) (fun i => k (![2, 0, 1, 3] i)) :=
    fun z hz => Set.mem_iInter.2 fun i =>
      (congrArg (fun q => q z ∈ D₀.P.L.U (k (![2, 0, 1, 3] i))) (hq₀ i)).mpr (hk _ hz)
  have e₂ : valR (FormalValue.basePt g ≫ φ) _ (s₀.f fun i => k (![2, 0, 1, 3] i)) = _ :=
    (congrArg (fun q => valR q _ (s₀.f fun i => k (![2, 0, 1, 3] i))) (hφ 2)).trans
      (FormalValue.valR_spMap ρ (show Sp S₀ ⟶ _ from g₀.b.left) _ cf _)
  have e₃ : FormalValue.coordVal g α jt = _ := (hg.2 jt k hd).trans (congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun i _ => valR_zpow _ _ (hd i) _ (![t 1, t 2, t 0, t 3] i)
      (by fin_cases i; exacts [ht 1, ht 2, ht 0, ht 3]) _)
    (valR_pullGen ρ (g₀.s α₀) k cg))
  have e₅ : (t 0 : S) ^ j * ∏ i, ((![t 1, t 2, t 0, t 3] i ^ (-Out.DegPre.gtε i) : Sˣ) : S) =
      ((∏ i, t i ^ Out.DegPre.famε j i : Sˣ) : S) := by
    rw [← Units.coe_prod, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← prod_factors t j]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  replace e₁ := e₁.trans (congrArg (κ r * ·) e₂)
  refine (congrArg₂ (fun a b => a ^ j * (_ * b)) (ht 0).symm e₃).trans ?_
  rw [← e₅] at e₁
  rw [map_mul, ← _root_.mul_assoc (κ r)]
  refine Eq.trans ?_ (congrArg (· * _) e₁)
  exact (congrArg (_ * ·) (_root_.mul_left_comm _ _ _)).trans
    ((_root_.mul_assoc _ _ _).symm.trans (_root_.mul_assoc _ _ _).symm)

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (j : ℕ) (x : a.D₀.X) (s₀ : a.D₀.SecB j x) (f : W.P.D.toPre.SecB j (W.e x)) (r : ℂ⟦X⟧) (jM : W.P.D.toPre.P.L.ι) (jf jt : Fin 4 → W.P.D.toPre.P.L.ι) (jt₀ : Fin 4 → a.D₀.P.L.ι), TanRel W ν g₁ → IsConstMul W j x s₀ f r → FormalValue.CohCharts g₁ (W.e x) jM jf jt → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀ → valR (A := DualNumber ℂ⟦X⟧) g₁.b.left _ (W.w.s (fun _ => jt₀ 2, jM)).val ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e x) jt) = TrivSqZeroExt.inl r * constEps (valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB x) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀) ((ν.s x).s jt₀).val) := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W ν g₁ j x s₀ f r jM jf jt jt₀ hg hf hj hc
  have := isLocalRing_dual ℂ⟦X⟧
  exact core (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧)) constEps W.w g₁ ν (hg x) s₀ f r (fun p => hf _ p _) jM jf jt jt₀
    hj hc

end GlobalTheory.ConstTanAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentEqFormalPointTransported
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

namespace GlobalTheory.ConstTanFormal

theorem corr_of_genRelR {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    {B B₀ Y₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen)
    (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt' : K → (Sp A' ⟶ B)}
    {pt₀ : K → (Y₀ ⟶ B₀)} {g : LB.Gen (LB.LinComb M pt ε)} {t : LB.Gen (LB.LinComb M pt' ε)}
    {ν : LB.Gen (LB.LinComb M₀ pt₀ ε)} (hg : g.IsGen) (ht : t.IsGen) (hν : ν.IsGen) {r : Sp A' ⟶ Sp A}
    {κ : Sp A ⟶ Y₀} {κ' : Sp A' ⟶ Y₀} (hκ : r ≫ κ = κ') (hp : ∀ k, pt' k = r ≫ pt k)
    (h : GenRelR w g (LB.pullGen _ _ _ ν κ)) (h' : GenRelR w t (LB.pullGen _ _ _ ν κ')) :
    LB.Gen.Corr M _ _ _ _ t (LB.pullGen M _ _ g r) := by
  have hw' := (isGen_iff w).1 hw
  have H := ConstGrp.pmaps_of_genRelR hw' hM hM₀ hg (DVR.pullGen_isGen _ _ _ _ hν κ) h
  have H' := ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht (DVR.pullGen_isGen _ _ _ _ hν κ') h'
  refine corr_of_val hM fun y J' hJ' => ?_
  choose J hJ using fun ψ : Sp A' ⟶ B₀ => exists_chart hM₀ (ψ y)
  have v := CubTransport.val_pmaps (fun k => (h.1 k).trans (Category.id_comp _).symm) H r hJ hJ'
  have v' := CubTransport.val_pmaps (fun k => (h'.1 k).trans (Category.id_comp _).symm) H' (𝟙 _) hJ hJ'
  rw [val_pull hJ, Category.comp_id, hκ] at v
  rw [val_pull hJ, Category.comp_id, Category.id_comp] at v'
  rw [val_pull hJ', Category.id_comp]
  simp only [Category.id_comp, hp] at v'
  exact mul_left_cancel (v'.symm.trans v)

theorem dualMapR_surjective {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'} (h : Function.Surjective φ) :
    Function.Surjective (dualMapR φ) := fun a => by
  obtain ⟨x, hx⟩ := h a.fst
  obtain ⟨y, hy⟩ := h a.snd
  exact ⟨TrivSqZeroExt.inl x + TrivSqZeroExt.inr y, by ext <;> simp [hx, hy]⟩

theorem ker_dualMapR_mk {R : Type} [CommRing R] (I : Ideal R) :
    RingHom.ker (dualMapR (Ideal.Quotient.mk I)) ≤ I.map (algebraMap R (DualNumber R)) := fun a ha => by
  have h₁ : a.fst ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (by
    simpa using congrArg TrivSqZeroExt.fst (RingHom.mem_ker.1 ha))
  have h₂ : a.snd ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (by
    simpa using congrArg TrivSqZeroExt.snd (RingHom.mem_ker.1 ha))
  have e : a = algebraMap R (DualNumber R) a.fst + algebraMap R (DualNumber R) a.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ h₁) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h₂))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (g : ℕ) (ex₀ : (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W ex₀ z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W g ex₀ z₀ ν v g₁ hD hT
  refine FormalValue.isFormalPt_of_surjective _ fun e => ?_
  let I : Ideal ℂ⟦X⟧ := Ideal.span {PowerSeries.X}
  have hI : I ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact PowerSeries.X_prime.not_isUnit
  have : IsLocalRing (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := isLocalRing_quotient_pow hI e
  have := isLocalRing_dual (ℂ⟦X⟧ ⧸ I ^ (e + 1))
  have := isLocalRing_dual ℂ⟦X⟧
  let ρ : DualNumber ℂ⟦X⟧ →+* DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := dualMapR (Ideal.Quotient.mk _)
  let s : Sp (DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1))) ⟶ Sp (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := spMap (algebraMap _ _)
  have hs : s ≫ Out.thick ℂ⟦X⟧ I e = spMap ρ ≫ (epsR ℂ⟦X⟧).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun r => (dualMapR_inl (Ideal.Quotient.mk (I ^ (e + 1))) r).symm)
  let xe : Sp (DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1))) ⟶ (Out.thickObj ℂ⟦X⟧ I e W.t.G).left :=
    pullback.lift (spMap ρ ≫ v.left) s (by rw [Category.assoc, Over.w v, hs])
  have hx : xe ≫ (Out.fstG I e W.t.G).left = spMap ρ ≫ v.left := pullback.lift_fst _ _ _
  have hx' : xe ≫ ((Over.map (Out.thick ℂ⟦X⟧ I e)).obj (Out.thickObj ℂ⟦X⟧ I e W.t.G)).hom =
      spMap ρ ≫ (epsR ℂ⟦X⟧).hom :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (pullback.lift_snd _ _ _)).trans hs)
  have hκ : spMap ρ ≫ spMap constEps = spMap (ρ.comp constEps) := (Spec.map_comp _ _).symm
  have h' := hD.2.2 e ρ (ρ.comp constEps) xe (dualMapR_inl _) (dualMapR_eps _)
    (fun r => (congrArg ρ (dualMapR_inl _ r)).trans (dualMapR_inl _ _))
    ((congrArg ρ (dualMapR_eps _)).trans (dualMapR_eps _)) hx
  have hp : ∀ x k, xe ≫ W.P.D.toPre.Oφ (W.P.U.gt e).pG (W.e x) k =
      spMap ρ ≫ Out.DegPre.gtφT W.P.D.toPre (epsR ℂ⟦X⟧) g₁.b (W.e x) k := fun x k => by
    refine W.spec.1.1.hom_ext ?_ ?_
    · refine ((h' x).1 k).trans ?_
      exact (congrArg (· ≫ _) hκ.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap ρ ≫ ·) ((hT x).1 k).symm).trans (Category.assoc _ _ _).symm))
    · rw [Category.assoc, Category.assoc]
      refine Eq.trans ?_ (hx'.trans ?_)
      · refine congrArg (xe ≫ ·) ?_
        fin_cases k <;> exact Over.w _
      · refine congrArg (spMap ρ ≫ ·) ?_
        fin_cases k <;> exact (Over.w _).symm
  refine ⟨_, inferInstance, ρ, xe, dualMapR_surjective Ideal.Quotient.mk_surjective, ?_, hx, hp 0 2, fun y => ?_⟩
  · rw [idealEps, ← Ideal.map_pow]
    exact ker_dualMapR_mk _
  · obtain ⟨x, rfl⟩ := W.e.surjective y
    exact corr_of_genRelR W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB (g₁.isGen _)
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt e).t_gen _) xe) (ν.isGen x) hκ (hp x) (hT x) (h' x)

end GlobalTheory.ConstTanFormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentReductionEqOrigin
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanRed
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

theorem comp_gtφT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T' : Over (Sp R)} (ρ : T' ⟶ T)
    (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A) (hb : ρ ≫ b = b') (χ : D.X) (k : Fin 4) :
    ρ.left ≫ DegPre.gtφT D T b χ k = DegPre.gtφT D T' b' χ k := by
  subst hb
  fin_cases k
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul ρ (cP D T χ) b).trans
      (congrArg (· * (ρ ≫ b)) (comp_cP D ρ χ)))
  · exact congrArg (fun q => q.left) (comp_cP D ρ χ)
  · rfl
  · exact congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one ρ)

theorem val_eq_of_genRelR {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    {B B₀ Y Y' : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen)
    (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt' : K → (Sp A' ⟶ B)}
    {ψ : K → (Y ⟶ B₀)} {ψ' : K → (Y' ⟶ B₀)} {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)}
    {u : LB.Gen (LB.LinComb M₀ ψ ε)} {u' : LB.Gen (LB.LinComb M₀ ψ' ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (hu : u.IsGen) (hu' : u'.IsGen) {h : Sp A ⟶ Y} {h' : Sp A' ⟶ Y'} (H : GenRelR w t (LB.pullGen _ _ _ u h))
    (H' : GenRelR w t' (LB.pullGen _ _ _ u' h')) (q : Sp A ⟶ Sp A') (hq : ∀ k, q ≫ pt' k = pt k)
    {Z : Scheme.{0}} (r : Z ⟶ Sp A) (z : Z)
    (hv : ∀ J, Good M₀ z J → val u' ((r ≫ q) ≫ h') z J = val u (r ≫ h) z J) {J'} (hJ' : Good M z J') :
    val t' (r ≫ q) z J' = val t r z J' := by
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists M₀ hM₀ z
  have hw' := (isGen_iff w).1 hw
  have e := CubTransport.val_pmaps (fun k => (H.1 k).trans (Category.id_comp _).symm)
    (ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht (pullGen_isGen _ _ _ _ hu h) H) r hJ hJ'
  have e' := CubTransport.val_pmaps (fun k => (H'.1 k).trans (Category.id_comp _).symm)
    (ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht' (pullGen_isGen _ _ _ _ hu' h') H') (r ≫ q) hJ hJ'
  rw [val_pull hJ, Category.comp_id] at e e'
  rw [hv J hJ, e] at e'
  simp only [Category.assoc r q, hq] at e'
  exact (mul_left_cancel e').symm

theorem corr_pull_of_valR {A F : Type} [CommRing A] [IsLocalRing A] [Field F] (p : A →+* F) [IsLocalHom p]
    {B : Scheme.{0}} {M : LB B} (hM : M.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp F ⟶ B)}
    {pt' : K → (Sp A ⟶ B)} (t : LB.Gen (LB.LinComb M pt ε)) (t' : LB.Gen (LB.LinComb M pt' ε))
    (hp : ∀ k, spMap p ≫ pt' k = pt k)
    (hv : ∀ j, ⊤ ≤ LB.wchart M pt' j → p (valR (𝟙 (Sp A)) (LB.wchart M pt' j) (t'.s j).val) =
      valR (𝟙 (Sp F)) (LB.wchart M pt j) (t.s j).val) :
    LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ t' (spMap p)) t := by
  refine corr_of_val hM fun y J hJ => ?_
  obtain rfl : y = cpt F := Subsingleton.elim (α := PrimeSpectrum F) _ _
  have hc : spMap p (cpt F) = cpt A := IsLocalRing.comap_closedPoint p
  rw [val_pull hJ, Category.id_comp, val_of t' _ _ J (fun k => J (pt k)) (fun k => by rw [hp]),
    val_of t _ _ J (fun k => J (pt k)) (fun k => by rw [Category.id_comp])]
  have m : ⊤ ≤ (𝟙 (Sp F)) ⁻¹ᵁ LB.wchart M pt (fun k => J (pt k)) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun k => hJ (pt k))
  have m' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart M pt' (fun k => J (pt k)) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun k => by
      have := hJ (pt k)
      rw [← hc]
      exact (congrArg (fun q => q (cpt F) ∈ M.U (J (pt k))) (hp k)).mpr this)
  have m'' := FormalValue.top_le_comp m' (spMap p)
  have e := FormalValue.valR_spMap p _ _ m' (t'.s (fun k => J (pt k))).val
  rw [Category.comp_id] at m'' e
  refine Units.ext ?_
  exact (toStkA_valR _ _ _ m'' _).symm.trans ((congrArg _ (e.trans (hv _ m'))).trans (toStkA_valR _ _ _ m _))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (Ξ : ConstPts W Λ) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v.left = (Ξ.x 0).left := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ g h z₀ ν Ξ v g₁ hd ht hf
  haveI := isLocalRing_dual ℂ
  haveI := isLocalRing_dual ℂ⟦X⟧
  let p : DualNumber ℂ⟦X⟧ →+* ℂ⟦X⟧ := (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom
  let p₀ : DualNumber ℂ →+* ℂ := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
  haveI : IsLocalHom p₀ := ⟨fun x hx => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hx⟩
  obtain ⟨h₁, h₂, -⟩ := hd
  have h₁' := h₁.1
  simp only [map_zero] at h₁' h₂
  have sq : spMap p ≫ spMap constEps = spMap (PowerSeries.C (R := ℂ)) ≫ spMap p₀ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun x => fst_dualMapR _ x)
  let ρ₀ : TF (R := ℂ) ℂ ⟶ epsR ℂ := Over.homMk (spMap p₀) (by
    show spMap p₀ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
      spMap (algebraMap (FractionRing ℂ) ℂ) ≫ spMap (algebraMap ℂ (FractionRing ℂ))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
    rfl)
  let ρ : selfR ⟶ epsR ℂ⟦X⟧ := Over.homMk (spMap p) (by
    show spMap p ≫ spMap (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧)) = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl)
  have hb₀ : ρ₀ ≫ ν.b = (Λ.ex0 0).b := Over.OverMorphism.ext h₁'
  have hb : ρ ≫ g₁.b = (Ξ.g 0).b := Over.OverMorphism.ext (W.spec.1.1.hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (spMap p ≫ ·) ((ht 0).1 2)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ν.b.left) sq).trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) h₁').trans ((Ξ.g_rel 0 0).1 2).symm))))))
    ((Over.w _).trans (Over.w _).symm))
  have hc : ∀ x, LB.Gen.Corr a.D₀.P.L _ _ _ _ (LB.pullGen a.D₀.P.L _ _ (ν.s x) (spMap p₀)) ((Λ.ex0 0).s x) :=
    fun x => corr_pull_of_valR p₀ a.D₀.P.isLB _ _ (comp_gtφT a.D₀ ρ₀ ν.b _ hb₀ x) fun j hj =>
      (congrArg p₀ (h₂ x j hj)).trans ((TrivSqZeroExt.fst_add _ _).trans (add_zero _))
  have hv : ∀ y (Z : Scheme.{0}) (r : Z ⟶ Sp ℂ⟦X⟧) (z : Z) J', Good W.P.D.toPre.P.L z J' →
      val (g₁.s y) (r ≫ spMap p) z J' = val ((Ξ.g 0).s y) r z J' := fun y Z r z J' hJ' => by
    obtain ⟨x, rfl⟩ := W.e.surjective y
    refine val_eq_of_genRelR W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB ((Ξ.g 0).isGen _) (g₁.isGen _)
      ((Λ.ex0 0).isGen x) (ν.isGen x) (Ξ.g_rel 0 x) (ht x) (spMap p) (comp_gtφT W.P.D.toPre ρ g₁.b _ hb _) r z
      (fun J hJ => ?_) hJ'
    have e : (r ≫ spMap p) ≫ spMap constEps = (r ≫ spMap (PowerSeries.C (R := ℂ))) ≫ spMap p₀ := by
      rw [Category.assoc, sq, Category.assoc]
    exact (congrArg (fun q => val (ν.s x) q z J) e).trans ((val_pull hJ _ _ _).symm.trans (val_corr hJ (hc x) _))
  let I : Ideal ℂ⟦X⟧ := (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)
  haveI : IsAdicComplete I ℂ⟦X⟧ := by
    simp only [I]
    rw [Algebra.algebraMap_self, Ideal.map_id]
    infer_instance
  refine hom_ext_of_isHausdorff I fun e => ?_
  obtain ⟨xe, hxe⟩ := FormalValue.exists_lift_thick (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}) W.t.G
    (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (ρ ≫ v).left (Over.w (ρ ≫ v)) e
  have hs : spMap ((Ideal.Quotient.mk (I ^ (e + 1))).comp p) = adicLevelι I (e + 1) ≫ spMap p := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hk : idealEps ^ (e + 1) ≤ RingHom.ker ((Ideal.Quotient.mk (I ^ (e + 1))).comp p) := fun s hs => by
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    simp only [I]
    rw [Algebra.algebraMap_self, Ideal.map_id, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (mem_idealEps_pow hs).1
  have H₁ := hf.hasCoords _ hk (xe := xe) (hxe.trans (by rw [hs, Category.assoc]; rfl))
  rw [hs] at H₁
  obtain ⟨k₁, k₂⟩ := (FormalPoint.hasCoords_iff W.P.U.toUnifPre e g₁ _ xe).1 H₁.2
  have H₂ : FormalPoint.HasCoords W.P.U.toUnifPre e (Ξ.g 0) (adicLevelι I (e + 1)) xe :=
    (FormalPoint.hasCoords_iff W.P.U.toUnifPre e _ _ xe).2
      ⟨k₁.trans ((Category.assoc _ _ _).trans (congrArg (fun q => adicLevelι I (e + 1) ≫ q.left) hb)),
        fun y z J hJ => (k₂ y z J hJ).trans (hv y _ _ z J hJ)⟩
  exact hxe.symm.trans ((Ξ.x_pt 0).comp_fstG_eq H₂)

end GlobalTheory.ConstTanRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantTorusExtensionTangentRel
section
namespace GlobalTheory.ConstTan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem exists_tanRel : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)), ∃ g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧), TanRel W ν g₁ := by
  intro _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W ν
  haveI := isLocalRing_dual ℂ⟦X⟧
  obtain ⟨gp, hw, -, -, hc, -⟩ := W.spec
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_genRelR (A := DualNumber ℂ⟦X⟧) globalFns_holds gp hw
    W.e.symm.toAddEquiv.toAddMonoidHom
    (fun y => by have := hc (W.e.symm y); rwa [LinearEquiv.apply_symm_apply] at this)
    (T := epsR ℂ) (spMap (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧))) (spMap constEps)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun r => dualMapR_inl _ r)).trans (spMap_comp _ _))) ν
  refine ⟨g, fun x => ?_⟩
  have := hg (W.e x)
  rw [show W.e.symm.toAddEquiv.toAddMonoidHom (W.e x) = x from W.e.symm_apply_apply x] at this
  exact this

end GlobalTheory.ConstTan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLatticeVectorRepAndShift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.GtRep

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem exists_rep_and_shift : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (k : ℕ), 1 ≤ k → (∀ p, ∃ la, Λ.Rep k p la) ∧ ∀ p la e, Λ.Rep k p la → ∃ q : Out.QkPt a.D₀ ℂ k, q.y = Λ.ε (la + k • e).y ∧ q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)) ∧ ∀ q', QkExt (algebraMap _ ℂ) p q' → Out.QkPt.Equiv a.D₀ ℂ q q' := by
  intro h1 h2 E _ _ _ H _ D l c O _ β _ _ b a Λ k hk
  obtain ⟨hadd, hsurj, -⟩ := GlobalTheory.T.analyticDictionaryExp_additive_surjective_linear h1 h2 E H D l c O β b a Λ
  obtain ⟨hker, hio, -⟩ := GlobalTheory.T.analyticDictionaryExp_kernel_iota_torusPoints E H D l c O β b a Λ
  have hB := a.bimult
  let ex : Λ.A.V →+ Out.GtPtF a.D₀ ℂ :=
    AddMonoidHom.mk' Λ.ex0 fun z z' => (isAdd_iff_eq _ _ _).1 (hadd z z')
  have hex : ∀ z, Λ.ex0 z = ex z := fun _ => rfl
  have hio' : ∀ la : Λ.A.La, ex (Λ.A.P0 la) = iota hB ℂ (Λ.ε la.y) := fun la => (isIota_iff_eq hB _ _).1 (hio la)
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hf : (algebraMap (FractionRing ℂ) ℂ).comp (algebraMap (FractionRing ℂ) (FractionRing ℂ)) =
      algebraMap (FractionRing ℂ) ℂ := RingHom.ext fun _ => rfl
  have hkk : ∀ v : Λ.A.V, (k : ℂ)⁻¹ • k • v = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hkk' : ∀ v : Λ.A.V, k • (k : ℂ)⁻¹ • v = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  refine ⟨fun p => ?_, fun p la e hrep => ?_⟩
  · obtain ⟨q, -, huniq⟩ := existsUnique_qkExt hB _ hf p
    obtain ⟨z, hz⟩ := hsurj q.g
    let l0 : Λ.A.La := AnArc.La.mk (Λ.ε.symm q.y) 0 0
    have hl0 : Λ.ε l0.y = q.y := Λ.ε.apply_symm_apply _
    have hzero : (Λ.ex0 (k • z - Λ.A.P0 l0)).IsZero := by
      rw [isZero_iff_eq, hex, map_sub, map_nsmul, ← hex z, hz, qk_nsmul hB, hio', hl0, sub_self]
    obtain ⟨l1, hl1, hl1'⟩ := (hker _).1 hzero
    refine ⟨l1 + l0, fun q' hq' => ?_⟩
    obtain rfl := huniq q' hq'
    refine ⟨by rw [AnArc.La.add_y, hl1, zero_add, hl0], ?_⟩
    rw [map_add, ← hl1', sub_add_cancel, hkk, hz]
  · refine ⟨qkMk hB (Λ.ε (la + k • e).y) (Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)))
      (by rw [hex, ← map_nsmul, hkk', hio']), rfl, rfl, fun q' hq' => ?_⟩
    obtain ⟨hy, hg⟩ := hrep q' hq'
    refine equiv_symm hB ((equiv_iff hB _ _).2 ⟨Λ.ε e.y, ?_, ?_⟩)
    · rw [qkMk_y, hy, AnArc.La.add_y, AnArc.La.nsmul_y, map_add, map_nsmul]
    · rw [qkMk_g, hg, hex, hex, map_add, map_nsmul, smul_add, hkk, map_add, hio']

end GlobalTheory.GtRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRigidifiedIsoAgreeAbelianFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f), (∃ w, IsRigIso m.cm t'.PP t.PP w) ∧ ∀ (w w' : LB.Iso t'.PP.L (t.PP.L.pull m.φ)), IsRigIso m.cm t'.PP t.PP w → IsRigIso m.cm t'.PP t.PP w' → ∀ (F : Type) [Field F] (y : Sp F ⟶ S') (x : Over.mk y ⟶ t'.G), IsProper (pullback.snd t'.G.hom y) → ∀ j j', ⊤ ≤ x.left ⁻¹ᵁ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') → valR x.left _ (w.s (fun _ => j, j')).val = valR x.left _ (w'.s (fun _ => j, j')).val := by
  first | exact @GlobalTheory.RigIso.main | exact GlobalTheory.RigIso.main | (intros; apply GlobalTheory.RigIso.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpEqOfIsometryMatchingMarkingsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_eq_of_isometry_matching_markings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (P P' : (Fu.Di i).La →+ (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (inferInstance : StarRing (𝓞 E)) = H.starRing → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i) ty P' → (∀ u v, (Fu.Di i).EF (gam u) (gam v) = (Fu.Di i).EF u v) → (∀ v ∈ idealPart D l, ∃ e, gam (Fu.t i v) = Fu.t i v + l.M • e) → (∀ v, ∃ e, gam (Fu.t i v) = Fu.t i v + l.A • e) → (∀ u, P' (gam u) = h (P u)) → Fu.u i P = Fu.u i P' ∧ ∀ z, (Fu.ex i P' (h z)).left = (Fu.ex i P z).left := by
  first | exact @GlobalTheory.ArcPts.exp_eq_of_matching_markings | exact GlobalTheory.ArcPts.exp_eq_of_matching_markings | (intros; apply GlobalTheory.ArcPts.exp_eq_of_matching_markings <;> assumption)
end

