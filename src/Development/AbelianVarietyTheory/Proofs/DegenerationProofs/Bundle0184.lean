import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitOverOfHasArcData
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomAlgebraisingThickeningsProjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MorAlgIdeal

open GlobalTheory.MorAlg

theorem exists_section (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    (hI : I ≠ ⊤) (hc : IsAdicComplete I R) (Y P : Over (Spec (CommRingCat.of R))) (q : P ⟶ Y)
    [IsSeparated q.left] [IsProper Y.hom] [Flat Y.hom] (hP : IsProjBy P.hom)
    (j : ∀ e, (thickObj R I e Y).left ⟶ P.left)
    (hq : ∀ e, j e ≫ q.left = pullback.fst Y.hom (thick R I e))
    (hj : ∀ e, thickMap R I e Y ≫ j (e + 1) = j e) :
    ∃ g : Y ⟶ P, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = j e := by
  obtain ⟨H, hH, n, s, hs⟩ := hP
  have hL : ∀ e, (H.pull (j e)).IsLB := fun e => LB.isLB_pull hH _
  choose t ht using fun e => exists_isPull (j e) hH s
  have hv : ∀ e, IsPull (thickMap R I e Y) (t (e + 1)) (t e) := fun e =>
    IsPull.cancel hH (hL _) (hL _) (ht (e + 1)) (by rw [hj]; exact ht e)
  choose v hv cv using hv
  have hjR : ∀ e, j e ≫ P.hom = (thickObj R I e Y).hom ≫ thick R I e := fun e => by
    rw [← Over.w q, ← Category.assoc, hq]
    exact pullback.condition
  have hci : ∀ e, IsClosedImmersion (thick R I e) := fun e =>
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hva : VeryAmpleBy (thickObj R I 0 Y).hom (H.pull (j 0)) (t 0) := by
    obtain ⟨w, hw, c⟩ := ht 0
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R P.left P.hom H n s hH hs _ (Ideal.Quotient.mk (I ^ (0 + 1))) _ _ (j 0) (hjR 0) ?_ _ w _
      (hL 0) hw c
    have h₁ : IsClosedImmersion (j 0 ≫ q.left) := by
      rw [hq]
      have := hci 0
      infer_instance
    have h₂ : IsClosedImmersion (j 0) := IsClosedImmersion.of_comp _ q.left
    have h₃ : IsClosedImmersion (pullback.lift (j 0) (thickObj R I 0 Y).hom (hjR 0) ≫
        pullback.fst P.hom (thick R I 0)) := by
      rw [pullback.lift_fst]
      exact h₂
    exact IsClosedImmersion.of_comp _ (pullback.fst P.hom (thick R I 0))
  have hpb : ∀ e, IsPullback (thickMap R I e Y) (thickObj R I e Y).hom (thickObj R I (e + 1) Y).hom
      (thickTrans R I e) := fun e => by
    refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick R I (e + 1))) (h₂₂ := thick R I (e + 1))
      (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [thickTrans_comp, pullback.lift_fst, Category.comp_id]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨B, H', s', b, w, hH', hs', hb, -, hw, heq⟩ := GlobalTheory.Degen.exists_projective_of_formal_embedding_local R I hI hc (fun e => thickObj R I e Y)
    (fun e => thickMap R I e Y) hpb (fun e => inferInstanceAs (Flat (pullback.snd Y.hom (thick R I e))))
    (fun e => H.pull (j e)) v (fun e => ⟨hL e, hv e⟩) n t cv hva
  obtain ⟨φ, u, hφ, hu, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy R P.left P.hom H n s hH hs B.left B.hom H' s' hH' hs'.1
    fun d F hF h0 => heq d F hF fun e k => by
      rw [← hjR]
      exact (ht e).eqn P.hom hH hF h0 k
  have hbφ : ∀ e, b e ≫ φ = j e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := IsPull.comp hH hH' (hL e) ⟨u, hu, cu⟩ ⟨w e, (hw e).1, (hw e).2⟩
    obtain ⟨w₂, hw₂, c₂⟩ := ht e
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections R P.left P.hom H n s hH hs _ _ (t e) _ _ w₁ w₂ (hL e) ?_ hw₁ hw₂ c₁ c₂
    rw [Category.assoc, hφ, hjR]
    exact (hb e).w
  let φ' : B ⟶ P := Over.homMk φ hφ
  have hbp : ∀ e, b e ≫ (φ' ≫ q).left = pullback.fst Y.hom (thick R I e) := fun e => by
    rw [← hq, ← hbφ]
    exact (Category.assoc _ _ _).symm
  have hB : IsProper ((φ' ≫ q).left ≫ Y.hom) := by
    rw [Over.w]
    exact GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ ⟨H', hH', n, s', hs'⟩
  have hp : IsProper (φ' ≫ q).left := IsProper.of_comp _ Y.hom
  have hiso : IsIso (φ' ≫ q) := GlobalTheory.IsoLimitIdeal.main R I hI B Y (φ' ≫ q) fun e => by
    have h₁ : (hb e).isoPullback.hom ≫ ((Over.pullback (thick R I e)).map (φ' ≫ q)).left = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst, Category.id_comp]
        rw [← hbp e, IsPullback.isoPullback_hom_fst_assoc]
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_snd, Category.id_comp]
        exact (hb e).isoPullback_hom_snd
    have h₂ : IsIso ((Over.forget _).map ((Over.pullback (thick R I e)).map (φ' ≫ q))) :=
      @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ (Iso.isIso_hom _) (IsIso.id _) h₁
    exact isIso_of_reflects_iso _ (Over.forget _)
  refine ⟨inv (φ' ≫ q) ≫ φ', fun e => ?_⟩
  rw [← hbp, Category.assoc, ← Over.comp_left, IsIso.hom_inv_id_assoc]
  exact hbφ e

theorem exists_hom_of_thickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y Z : Over (Spec (CommRingCat.of R))), IsProjBy Y.hom → IsProjBy Z.hom → Flat Y.hom → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Z.left, (∀ e, f e ≫ Z.hom = pullback.fst Y.hom (thick R I e) ≫ Y.hom) → (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ g : Y ⟶ Z, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = f e := by
  intro R _ _ _ I hI hcI Y Z hY hZ hfl f hf hc
  have pY := GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hY
  have pZ := GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hZ
  have hsep : IsSeparated (fst Y Z).left := inferInstanceAs (IsSeparated (pullback.fst Y.hom Z.hom))
  obtain ⟨g, hg⟩ := exists_section R I hI hcI Y (Y ⊗ Z) (fst Y Z) (GlobalTheory.AbLaw.isProjBy_tensor R Y Z hY hZ)
    (fun e => pullback.lift (pullback.fst Y.hom (thick R I e)) (f e) (hf e).symm)
    (fun e => pullback.lift_fst _ _ _) (fun e => by
      apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
      · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hc])
  refine ⟨g ≫ snd Y Z, fun e => ?_⟩
  have := congrArg (· ≫ pullback.snd Y.hom Z.hom) (hg e)
  exact ((Category.assoc _ _ _).symm.trans this).trans (pullback.lift_snd _ _ _)

end GlobalTheory.MorAlgIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLocaStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projective_algebraisation_formal_complete_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k'))) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (H' : LB B.left) (s' : Fin (n + 1) → LB.Sec H') (b : ∀ e, (Y e).left ⟶ B.left) (w : ∀ e, LB.Iso (H e) (H'.pull (b e))), H'.IsLB ∧ VeryAmpleBy B.hom H' s' ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (w e).IsGen ∧ (∀ j, (∀ z (k : (H').ι) (k' : (H e).ι), (b e) z ∈ (H').U k → z ∈ (H e).U k' → gs (b e) z _ ((s' j).f k) = (Geo.Tor.gw (w e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ e, (∀ k : (H e).ι, MvPolynomial.eval₂Hom (cst ((Y (e)).hom ≫ thick R I (e)) ((H e).U k)) (fun j => (s e j).f k) (F) = 0)) → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (B.hom) ((H').U k)) (fun j => (s' j).f k) (F) = 0) := by
  first | exact @GlobalTheory.Degen.exists_projective_of_formal_embedding_local | exact GlobalTheory.Degen.exists_projective_of_formal_embedding_local | (intros; apply GlobalTheory.Degen.exists_projective_of_formal_embedding_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalPrimeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_complete_local_normal_prime : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (t : SAB H (Sp R)), PolAt t (jK R) → SplitOver t.G I → ThetaNZ t.G t.PP.L → ∃ P : PELUnif I t, P.TorsionIso := by
  first | exact @GlobalTheory.LN.UnifPrime.exists_pelUnif | exact GlobalTheory.LN.UnifPrime.exists_pelUnif | (intros; apply GlobalTheory.LN.UnifPrime.exists_pelUnif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExtendedArcUAdicUniformisationOfArcData
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ArcData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sab {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem polAt_of_point {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ)
    {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = x ≫ χ) : PolAt t x := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull x t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t' : SAB H (Sp K)) (p : Sp K ⟶ Y.X) (_ : p = y ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t y) := by
    intro t' p hp n
    subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ hy.symm n
  have h₂ : LBIso PP'.L (t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper,
    amplePt _ _ y _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃) Y.oF.ample Y.oF.ktriv⟩

theorem admissible_maximal_ideal_of_complete_dvr_char_zero {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (h : CDvr V) :
    admitted V (IsLocalRing.maximalIdeal V) ∧ IsPrincipalIdealRing (V ⧸ IsLocalRing.maximalIdeal V) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V)
  exact ⟨⟨⟨inferInstance, inferInstance, inferInstance, h₂⟩, h₂, h₃, inferInstance, inferInstance⟩, inferInstance⟩

theorem cdvr_powerSeries (K : Type) [Field K] [CharZero K] : CDvr (PowerSeries K) := by
  refine ⟨inferInstance, ?_, algebraRat.charZero _⟩
  rw [PowerSeries.maximalIdeal_eq_span_X]
  infer_instance

theorem powerSeries_dvr_admissible_X_ideal (O : Type) [CommRing O] [IsDomain O] [CharZero O] [IsDiscreteValuationRing O]
    (h : IsAdicComplete (IsLocalRing.maximalIdeal O) O) :
    admitted (PowerSeries O) (Ideal.span {PowerSeries.X}) ∧
      IsPrincipalIdealRing (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O)}) := by
  have hk : Ideal.span {(PowerSeries.X : PowerSeries O)} = RingHom.ker (PowerSeries.constantCoeff (R := O)) := by
    ext f
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, RingHom.mem_ker]
  have e : (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O)}) ≃+* O :=
    (Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)
  refine ⟨⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, ?_,
    charZero_of_injective_ringHom (PowerSeries.C_injective (R := O)), hk ▸ RingHom.ker_isPrime _,
    IsIntegrallyClosed.of_equiv e.symm⟩, IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective⟩
  infer_instance

theorem hasArcData_trait (h₁ : Laws) (h₂ : Laws2) (h₃ : Laws3) (h₄ : Laws4) (h₅ : Laws5) (h₆ : Laws6) (hE : Ega)
    (hU : USt) (hP : PelSt) (hH : HomExtSt) {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
    {W₀ : ValuationSubring ℂ} (Y : Model Xo c (c.V W₀).subtype) {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O']
    {b : c.V W₀ →+* O'} (a : ArcIn D l (c.V W₀).subtype O' b) (hp : PushInvertible Y.t.G Y.t.PP.L)
    (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X) (hχ : jK _ ≫ χ = y ≫ Y.j)
    (hT : TraitData Y a (RingHom.id _) y) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V)
    (φ : PowerSeries O' →+* V) (hφ : Function.Injective φ) (hX : ¬ IsUnit (φ PowerSeries.X))
    (hC : ∀ x, x ≠ 0 → IsUnit (φ (PowerSeries.C x))) :
    Y.HasArcData a (IsLocalRing.maximalIdeal V) (φ.comp (PowerSeries.C (R := O'))) (φ PowerSeries.X) (spMap φ ≫ χ) := by
  have hinj : Function.Injective ((algebraMap V (FractionRing V)).comp φ) := (IsFractionRing.injective V _).comp hφ
  let gam : FractionRing (PowerSeries O') →+* FractionRing V := IsFractionRing.lift hinj
  have hg : ∀ r, gam (algebraMap _ _ r) = algebraMap V _ (φ r) := fun r => IsFractionRing.lift_algebraMap hinj r
  have hsq : spMap gam ≫ y ≫ Y.j = jK V ≫ spMap φ ≫ χ := by
    rw [← hχ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext r
    exact hg r
  obtain ⟨W, _, _, _, io, hW, hio, hfin, hA⟩ := (hT.2 V hV φ gam hg _ hsq).2 hX
  have hA' : Y.HasArcData a (IsLocalRing.maximalIdeal W) (io.comp (φ.comp (PowerSeries.C (R := O'))))
    (io (φ PowerSeries.X)) (spMap io ≫ spMap φ ≫ χ) := hA
  obtain ⟨t, ⟨m⟩⟩ := exists_sab (spMap φ ≫ χ) Y.t
  have hsq' : (spMap gam ≫ y) ≫ Y.j = jK V ≫ spMap φ ≫ χ := (Category.assoc _ _ _).trans hsq
  have hS := GlobalTheory.T.closedFibre_split_of_arcData_finite_extension h₁ h₂ h₃ h₄ h₅ h₆ E H D l Xo c W₀ Y O' b a V hV _ _ hC hX _ _ hsq' t m W hW io hio hfin hA'
  obtain ⟨hadm, hpid⟩ := admissible_maximal_ideal_of_complete_dvr_char_zero hV
  obtain ⟨P, hPt⟩ := GlobalTheory.LN.UnifPrime.exists_pelUnif h₁ h₂ h₃ h₄ h₅ hE hU hP E H V _ hadm hpid t (polAt_of_point Y m _ _ hsq') hS
    (GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible E H _ _ hp V _ t m)
  have := hV.2.2
  have hloc : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  exact GlobalTheory.T.arcData_descends_from_completeDVR h₁ h₂ h₃ h₄ h₅ h₆ hH E H D l Xo c W₀ Y O' b a V _ _ _ hadm.1
    (IsLocalRing.maximalIdeal.isMaximal V).ne_top (hφ.comp PowerSeries.C_injective) _ _ hsq' t m P hPt W hW io hio
    (IsLocalRing.map_maximalIdeal_le io) (fun h => hX (isUnit_of_map_unit io _ h)) (fun x hx => (hC x hx).map io) hA'

theorem hasArcData_of_traitData : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → PushInvertible Y.t.G Y.t.PP.L → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → Y.HasArcData a (Ideal.span {(PowerSeries.X : PowerSeries O')}) (PowerSeries.C (R := O')) PowerSeries.X χ := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hb hp y χ hχ hT
  rcases hb with ⟨hf, -⟩ | ⟨hd, hϖ, hc⟩
  · letI := hf.toField
    have h := hasArcData_trait h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH Y a hp y χ hχ hT (cdvr_powerSeries O') (RingHom.id _)
      Function.injective_id PowerSeries.X_prime.not_unit (fun x hx => (IsUnit.mk0 x hx).map (PowerSeries.C (R := O')))
    have e : spMap (RingHom.id (PowerSeries O')) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp, PowerSeries.maximalIdeal_eq_span_X] at h
    exact h
  · have hi := IsFractionRing.injective O' (FractionRing O')
    have hX : ¬ IsUnit (PowerSeries.map (algebraMap O' (FractionRing O')) PowerSeries.X) := by
      rw [PowerSeries.map_X]
      exact PowerSeries.X_prime.not_unit
    have hC : ∀ x, x ≠ 0 → IsUnit (PowerSeries.map (algebraMap O' (FractionRing O')) (PowerSeries.C x)) := fun x hx => by
      rw [PowerSeries.map_C]
      exact (IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 hx)).map _
    have hV := cdvr_powerSeries (FractionRing O')
    have h := hasArcData_trait h₁ h₂ h₃ h₄ h₅ h₆ hE hU hP hH Y a hp y χ hχ hT hV _
      (PowerSeries.map_injective _ hi) hX hC
    obtain ⟨t, ⟨m⟩⟩ := exists_sab χ Y.t
    have hS := GlobalTheory.splitOver_of_hasArcData h₁ h₂ h₃ hH E H D l Xo c W₀ Y O' b a hd χ t m (by
      have e : (PowerSeries.map (algebraMap O' (FractionRing O'))).comp (PowerSeries.C (R := O')) =
          (PowerSeries.C (R := FractionRing O')).comp (algebraMap O' _) := RingHom.ext fun x => PowerSeries.map_C (algebraMap O' (FractionRing O')) x
      rw [e, PowerSeries.map_X] at h
      exact h)
    obtain ⟨hadm, hpid⟩ := powerSeries_dvr_admissible_X_ideal O' (hϖ.maximalIdeal_eq ▸ hc)
    obtain ⟨P, hPt⟩ := GlobalTheory.LN.UnifPrime.exists_pelUnif h₁ h₂ h₃ h₄ h₅ hE hU hP E H _ _ hadm hpid t (polAt_of_point Y m _ _ hχ.symm) hS
      (GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible E H _ _ hp _ _ t m)
    have := hadm.2.2.1
    refine GlobalTheory.T.arcData_descends_from_completeDVR h₁ h₂ h₃ h₄ h₅ h₆ hH E H D l Xo c W₀ Y O' b a _ _ _ _ hadm.1 hadm.2.2.2.1.ne_top
      PowerSeries.C_injective _ _ hχ.symm t m P hPt _ hV _ (PowerSeries.map_injective _ hi) ?_ hX hC h
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    exact hX

end GlobalTheory.ArcData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianReductionAlongIsogenyStrictHenselian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.IsogRed

variable {S T : Scheme.{0}} (f : T ⟶ S)

noncomputable def sec {G : Over S} (s : 𝟙_ (Over S) ⟶ G) : 𝟙_ (Over T) ⟶ (Over.pullback f).obj G :=
  Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map s

theorem sec_comp {G G' : Over S} (s : 𝟙_ (Over S) ⟶ G) (I : G ⟶ G') :
    sec f (s ≫ I) = sec f s ≫ (Over.pullback f).map I := by
  simp only [sec, Functor.map_comp, Category.assoc]

theorem sec_pow {G : Over S} [GrpObj G] (s : 𝟙_ (Over S) ⟶ G) (n : ℕ) : sec f (s ^ n) = sec f s ^ n := by
  simp only [sec, ← MonObj.comp_pow]
  congr 1
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih]

theorem sec_left {G : Over S} (s : 𝟙_ (Over S) ⟶ G) :
    (sec f s).left ≫ pullback.fst G.hom f = f ≫ s.left := by
  have hw := Over.w (Functor.LaxMonoidal.ε (Over.pullback f))
  have hc := pullback.condition (f := (𝟙_ (Over S)).hom) (g := f)
  simp only [sec, Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
  simp at hw hc ⊢

theorem sec_eq {G : Over S} (s : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over T) ⟶ (Over.pullback f).obj G)
    (h : f ≫ s.left = x.left ≫ pullback.fst G.hom f) : sec f s = x := by
  ext1
  apply pullback.hom_ext
  · rw [sec_left, h]
  · have h1 := Over.w (sec f s)
    have h2 := Over.w x
    simp only [Over.pullback_obj_hom] at h1 h2
    rw [h1, h2]

theorem sec_injective [IsSchemeTheoreticallyDominant f] {G : Over S} [IsSeparated G.hom]
    {s t : 𝟙_ (Over S) ⟶ G} (h : sec f s = sec f t) : s = t := by
  refine GlobalTheory.over_ext_of_schemeTheoreticallyDominant (Y := 𝟙_ (Over S)) f ?_
  rw [← sec_left, ← sec_left, h]

theorem smConn_baseChange (G : Over S) [GrpObj G] (h : SmConn G) : SmConn ((Over.pullback f).obj G) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩ <;> (try simp only [Over.pullback_obj_hom]) <;> infer_instance

theorem sec_residue_surjective {R : Type} [CommRing R] [HenselianLocalRing R] (G : Over (Sp R)) [Smooth G.hom]
    (x : 𝟙_ _ ⟶ spFibre G) : ∃ s : 𝟙_ _ ⟶ G, sec (spMap (IsLocalRing.residue R)) s = x := by
  have hx : (x.left ≫ pullback.fst G.hom (spMap (IsLocalRing.residue R))) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ 𝟙 _ := by
    have hw := Over.w x
    simp only [Over.pullback_obj_hom] at hw
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    simp
  obtain ⟨⟨y, hy⟩, hyx⟩ := GlobalTheory.reducePoint_residue_surjective G.hom R (𝟙 _) ⟨_, hx⟩
  refine ⟨Over.homMk y (by simpa using hy), sec_eq _ _ _ ?_⟩
  simpa [GlobalTheory.reducePoint] using congrArg Subtype.val hyx

theorem relDim_spFibre {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (hG : SmConn G) (g : ℕ)
    (h : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj G).hom) :
    SmoothOfRelativeDimension g (spFibre G).hom := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{0} g) :=
    smoothOfRelativeDimension_isStableUnderBaseChange g
  have hG0 : SmoothOfRelativeDimension g G.hom := by
    apply GlobalTheory.GenericDim.smoothOfRelativeDimension_of_generic R G g
    unfold ReciprocityTheory.ChartRestriction.G.Out.jK
    obtain ⟨ψ, hψ⟩ : ∃ ψ : K →+* FractionRing R, ψ.comp (algebraMap R K) = algebraMap R (FractionRing R) :=
      ⟨_, (IsLocalization.algEquiv (nonZeroDivisors R) K (FractionRing R)).toAlgHom.comp_algebraMap⟩
    have hK : SmoothOfRelativeDimension g
        (pullback.snd G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := h
    rw [← hψ, CommRingCat.ofHom_comp, Spec.map_comp]
    have key : pullback.snd G.hom (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) =
        (pullbackLeftPullbackSndIso G.hom _ _).inv ≫
          pullback.snd (pullback.snd G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (Spec.map (CommRingCat.ofHom ψ)) := by
      rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]
    rw [key]
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension.{0} g)
      (hP := @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
        (smoothOfRelativeDimension_isStableUnderBaseChange g)) _ _).mpr
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (self := smoothOfRelativeDimension_isStableUnderBaseChange g) (IsPullback.of_hasPullback _ _) hK)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (self := smoothOfRelativeDimension_isStableUnderBaseChange g) (IsPullback.of_hasPullback _ _) hG0

theorem pow_comp_isogeny {Z A B : Over T} [GrpObj A] [GrpObj B] (i : A ⟶ B) (r : B ⟶ A) [IsMonHom i] {m : ℕ}
    (hri : r ≫ i = 𝟙 _ ^ m) (c : ℕ) (x : Z ⟶ B) : ((x ≫ r) ^ c) ≫ i = x ^ (m * c) := by
  rw [MonObj.pow_comp, Category.assoc, hri, MonObj.comp_pow, Category.comp_id, pow_mul]

theorem sec_eq_comp {G : Over S} {A : Over T} (e : (Over.pullback f).obj G ≅ A) (s : 𝟙_ (Over S) ⟶ G)
    (a : 𝟙_ (Over T) ⟶ A) (h : f ≫ s.left = a.left ≫ e.inv.left ≫ pullback.fst G.hom f) : sec f s = a ≫ e.inv := by
  apply sec_eq
  rw [h, Over.comp_left, Category.assoc]

theorem exists_section {G G' : Over S} [GrpObj G] [GrpObj G'] [IsSchemeTheoreticallyDominant f] [IsSeparated G'.hom]
    {A : Over T} [GrpObj A] (e : (Over.pullback f).obj G ≅ A) (i : A ⟶ (Over.pullback f).obj G')
    (r : (Over.pullback f).obj G' ⟶ A) [IsMonHom i] {m c : ℕ} (hri : r ≫ i = 𝟙 _ ^ m) (I : G ⟶ G')
    (hI : (Over.pullback f).map I = e.hom ≫ i)
    (hext : ∀ a : 𝟙_ _ ⟶ A, ∃ s : 𝟙_ _ ⟶ G, f ≫ s.left = (a ^ c).left ≫ e.inv.left ≫ pullback.fst G.hom f)
    (z : 𝟙_ _ ⟶ G') : ∃ s : 𝟙_ _ ⟶ G, s ≫ I = z ^ (m * c) := by
  obtain ⟨s, hs⟩ := hext (sec f z ≫ r)
  refine ⟨s, sec_injective f ?_⟩
  rw [sec_comp, sec_eq_comp f e s _ hs, hI, sec_pow, Category.assoc, e.inv_hom_id_assoc,
    pow_comp_isogeny i r hri]

theorem semiAbelian_reduction_of_isogeny : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] (G' : Over (Sp R)) [GrpObj G'] (g m : ℕ), IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → IsSemiAbelian G' → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj G').hom → ∀ (i : A ⟶ (Over.pullback (spMap (algebraMap R K))).obj G') (r : (Over.pullback (spMap (algebraMap R K))).obj G' ⟶ A), IsMonHom i → IsMonHom r → 1 ≤ m → r ≫ i = 𝟙 _ ^ m → ∃ (G : Over (Sp R)) (_ : GrpObj G) (e : (Over.pullback (spMap (algebraMap R K))).obj G ≅ A), SmConn G ∧ IsMonHom e.hom ∧ Nonempty (TorusExtension (spFibre G)) := by
  intro R K _ _ _ _ _ hSH A _ G' _ g m hA hP hG' hgA hgG' i r hi hr hm hri
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := id hG'
  have hSG' : SmConn G' := ⟨a1, a2, a3, a4, a5⟩
  have : IsCommMonObj A := hA.1
  obtain ⟨M, hMg, hM, he, c, hc, hext⟩ := GlobalTheory.T.exists_neutral_group_model' R K hSH A hA hP
  obtain ⟨hdvr, hhens, hac, hfr⟩ := hSH
  refine ⟨M.Y, hMg, M.e, hM, he, ?_⟩
  obtain ⟨F, ⟨hF, hFe⟩, -⟩ := GlobalTheory.T.existsUnique_hom_extension_smoothConn_semiAbelian_dvr R K M.Y G' hM hG' (M.e.hom ≫ i) inferInstance
  have hgM : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj M.Y).hom := by
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{0} g) :=
      smoothOfRelativeDimension_isStableUnderBaseChange g
    rw [← Over.w M.e.hom]
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension.{0} g)
      (hP := @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
        (smoothOfRelativeDimension_isStableUnderBaseChange g)) ((Over.forget _).mapIso M.e).hom A.hom).mpr hgA
  refine GlobalTheory.T.torusExtension_of_surjective_of_dim_eq' (IsLocalRing.ResidueField R) (spFibre M.Y) (spFibre G') g
    (smConn_baseChange _ _ hM) (smConn_baseChange _ _ hSG')
    (relDim_spFibre M.Y hM g hgM) (relDim_spFibre G' hSG' g hgG')
    (a6 _ _) ((Over.pullback (spMap (IsLocalRing.residue R))).map F) inferInstance ?_
  intro y
  obtain ⟨w, hw⟩ := GlobalTheory.T.torusExtension_points_divisible' (IsLocalRing.ResidueField R) (spFibre G') (a6 _ _) (m * c)
    (by simpa using Nat.mul_le_mul hm hc) y
  obtain ⟨z, hz⟩ := sec_residue_surjective G' w
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  obtain ⟨s, hs⟩ := exists_section (spMap (algebraMap R K)) M.e i r hri F hFe (fun a => hext a) z
  refine ⟨sec (spMap (IsLocalRing.residue R)) s, ?_⟩
  rw [← sec_comp, hs, sec_pow, hz, hw]

end GlobalTheory.IsogRed
end

