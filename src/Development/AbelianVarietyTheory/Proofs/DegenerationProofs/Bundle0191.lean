import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0188
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0137
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionCoordinatesEqDegenerationSeries
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinCombValueAct
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
noncomputable section
namespace GlobalTheory.ZH.SecComb
open GlobalTheory.ZH.SecValue

theorem pull_liftFun {S : Scheme.{0}} {A T : Over S} [GrpObj A] (ψ : T ⊗ A ⟶ T ⊗ A) (hψ : ψ ≫ fst T A = fst T A)
    {U W : (T ⊗ A).left.Opens} (h : W ≤ ψ.left ⁻¹ᵁ U) (r : Γ(T.left, ⊤)) :
    ((T ⊗ A).left.presheaf.map (homOfLE h).op).hom ((ψ.left.app U).hom (liftFun A U r)) = liftFun A W r := by
  have e : ψ.left ≫ (fst T A).left = (fst T A).left := by rw [← Over.comp_left, hψ]
  have e₁ : ∀ V : (T ⊗ A).left.Opens, liftFun A V r = ((fst T A).left.appLE ⊤ V le_top).hom r := fun _ => rfl
  rw [e₁, e₁]
  refine (congrArg (fun q => q.hom r) (Scheme.Hom.appLE_comp_appLE ψ.left (fst T A).left ⊤ U W le_top h)).trans ?_
  simp only [e]

theorem ring_sum {B B' C I : Type} [CommRing B] [CommRing B'] [CommRing C] [Fintype I] (f' : B' →+* C) (f : B →+* C)
    (u : C) {c s : I → B} {c' s' : I → B'} {t : B} {t' : B'} (ht : t = ∑ l, c l * s l) (ht' : t' = ∑ l, c' l * s' l)
    (hc : ∀ l, f' (c' l) = f (c l)) (h : ∀ l, f' (s' l) = u * f (s l)) : f' t' = u * f t := by
  rw [ht, ht', map_sum, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [map_mul, map_mul, h, hc, mul_left_comm]

theorem isTwistPull_sum {S : Scheme.{0}} {A T : Over S} [GrpObj A] {L : LB A.left} (ψ : T ⊗ A ⟶ T ⊗ A)
    (hψ : ψ ≫ fst T A = fst T A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α) {I : Type} [Fintype I]
    (c : I → Γ(T.left, ⊤)) {s : I → LB.Sec (LPow A L b T)} {s' : I → LB.Sec (LPow A L a T)}
    {t : LB.Sec (LPow A L b T)} {t' : LB.Sec (LPow A L a T)}
    (ht : ∀ j, t.f j = ∑ l, liftFun A _ (c l) * (s l).f j) (ht' : ∀ j, t'.f j = ∑ l, liftFun A _ (c l) * (s' l).f j)
    (h : ∀ l, IsTwistPull A L ψ m hm a b α (s l) (s' l)) : IsTwistPull A L ψ m hm a b α t t' := fun j =>
  ring_sum _ (RingHom.comp _ _) _ (ht _) (ht' _)
    (fun l => (res_liftHom A _ (c l)).trans (pull_liftFun ψ hψ (chart_le_pull A L ψ m hm j) (c l)).symm) fun l => h l j

section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem valM_zero (x) (e : FrAt x) : ValM (0 : SecM A.A A.L k (TFK (R := R) F)) x e 0 := fun z J hJ => by
  have h := ThetaAct.sv_add (0 : SecM A.A A.L k (TFK (R := R) F)) 0 (ptSecT A.A x).left z hJ
  rw [add_zero, left_eq_add] at h
  refine h.trans ?_
  simp only [id, CoefBasic.cst_eq, map_zero]
  exact (zero_mul (M₀ := (TFK (R := R) F).left.presheaf.stalk z) _).symm

theorem valM_sum {x} {e : FrAt x} {J : Type} (s : Finset J)
    {σ : J → SecM A.A A.L k (TFK (R := R) F)} {c : J → F} (h : ∀ l, ValM (σ l) x e (c l)) :
    ValM (∑ l ∈ s, σ l) x e (∑ l ∈ s, c l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valM_zero x e
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add ih

theorem exists_valAt (t : SecA A F k) {x} {e : FrAt x} (he : e.IsGen) : ∃ c, ValAt t x e c := by
  obtain ⟨w, hw⟩ := ThetaPtExist.exists_isValueAt A.isLB t x (powFrame A.A A.L x e k) (EvVal.powFrame_isGen A.A A.L x e he k)
  obtain ⟨c, rfl⟩ := kon_surj w
  refine ⟨c, fun z J hJ => ?_⟩
  have := ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ
  rw [Category.id_comp] at this
  exact this

end

theorem lin_comb_value_act : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), (∀ (t : SecA A F k) x (e : FrAt x), e.IsGen → ∃! a : F, ValAt t x e a) ∧ ∀ (I : Type) [Fintype I] (c : I → F) (s : I → SecA A F k), (∃ t, IsComb s c t) ∧ ∀ t, IsComb s c t → (∀ x (e : FrAt x) (a : I → F), (∀ i, ValAt (s i) x e (a i)) → ValAt t x e (∑ i, c i * a i)) ∧ ∀ (θ : ThetaGrp A.A A.L k (TFK (R := R) F)) (s' : I → SecA A F k) t', (∀ i, IsActOf A.A A.L k θ (s i) (s' i)) → IsComb s' c t' → IsActOf A.A A.L k θ t t' := by
  intro R _ _ A F _ _ k
  refine ⟨fun t x e he => ?_, fun I _ c s => ⟨?_, fun t ht => ⟨fun x e a ha => ?_, fun θ s' t' hs ht' => ?_⟩⟩⟩
  · obtain ⟨a, ha⟩ := exists_valAt t he
    exact ⟨a, ha, fun b hb => ValM.unique (σ := SecM.ofSec A.A t) hb ha⟩
  · exact ⟨SecM.toSec A.A (∑ l, kon R F (c l) • SecM.ofSec A.A (s l)), (isComb_iff _ _ _).2 rfl⟩
  · have h := valM_sum (Finset.univ : Finset I) fun l => ValM.smul (σ := SecM.ofSec A.A (s l)) (ha l) (c l)
    rw [← (isComb_iff _ _ _).1 ht] at h
    exact h
  · exact isTwistPull_sum _ (lift_fst _ _) _ _ _ _ _ (fun l => kon R F (c l)) ht ht' hs

end GlobalTheory.ZH.SecComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NuGeTranslatePullSmul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem eq_mul_of_isTwistPull {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    {m : T ⊗ A ⟶ A} {a b : ℤ} {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    {s s₀ : LB.Sec (LPow A L b T)} {t t₀ : LB.Sec (LPow A L a T)} {c : Γ(T.left, ⊤)}
    (e : ∀ j, s.f j = liftFun A _ c * s₀.f j)
    (h : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α s t)
    (h₀ : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α s₀ t₀) (j) :
    t.f j = liftFun A _ c * t₀.f j := by
  have f₁ : (lift (fst T A) m).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left, lift_fst]
  have key : (SecM.ofSec A t : SecM A L a T) = SecM.ofSec A (SecM.toSec A (c • SecM.ofSec A t₀)) :=
    VVRank.ofSec_ext A hL fun y J hJ => by
      rw [ThetaPtMove.sv_of_eq_mul (s := SecM.toSec A (c • SecM.ofSec A t₀)) (t := t₀) (c := c) (fun j => rfl) _ y hJ,
        VVRank.sv_of_isTwistPull A h _ y hJ, VVRank.sv_of_isTwistPull A h₀ _ y hJ,
        ThetaPtMove.sv_of_eq_mul e _ y hJ]
      simp only [Category.assoc, f₁]
      ring
  exact congrArg (fun q => q.1 j) key

theorem nuGe_translate_pull_smul : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th₀ : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th₀ ϑ → Prim D Q v ϑ → ∀ (m N : ℕ), N = m ^ 2 → Odd m → IsUnit (m : V) → ∀ (c : F) (r : ℚ) (th : SecA A F 1), (r : WithTop ℚ) ≤ v c → (∀ j, th.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * th₀.f j) → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := V) F) A.A).left, (snd (TFK (R := V) F) A.A ^ m).left] ![(N : ℤ), -((1 : ℕ) : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := V) F) ((N : ℤ) - 1)) → ∀ (s₁ t : SecA A F N) (x : TFK (R := V) F ⟶ A.A) (θ : ThetaGrp A.A A.L N (TFK (R := V) F)) (s : Fam D.toPre F N), IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) (N : ℤ) ((1 : ℕ) : ℤ) α th s₁ → x ^ N = 1 → SymLift A.A A.L N N x θ → IsActOf A.A A.L N θ s₁ t → U.ExpandsF F N w₀ t s → NuGe D Q F v N s r := by
  intro hLL hBC hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th₀ ϑ hth hprim m N hNm hm hmu
    c r th hr eth α hα hn s₁ t x θ s hs₁ hx hθ ht hs
  subst hNm
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  obtain ⟨hB, hlin⟩ := expBijF_and_expandsF_lin hLL V _ hA D A G hG U
  obtain ⟨hB₁, -⟩ := hB F (m ^ 2) hN1 w₀ hN.1
  let T := TFK (R := V) F
  let κ : F ≃+* Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  obtain ⟨u₁, hu₁⟩ := VVRank.exists_isTwistPull A.A (ψ := mulT A.A T m) (hm := lift_snd _ _) A.isLB hα th₀
  obtain ⟨t₀, ht₀⟩ := VVRank.exists_isTwistPull A.A (ψ := translT A.A θ.pt) (hm := lift_snd _ _) A.isLB θ.isGen u₁
  obtain ⟨c₀, hc₀⟩ := NormTheta.exists_value A.isLB hN.2.1 _ t₀
  obtain ⟨c', rfl⟩ := κ.surjective c₀
  obtain ⟨s₀, hs₀, -⟩ := hB₁ t₀
  have hP := GlobalTheory.T.primitive_expansion_thetaPullback_heisenbergTranslates hLL hBC hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th₀ ϑ hth hprim m hm hmu
    x t₀ c' s₀ hx ⟨α, u₁, θ, hα, hn, hu₁, hθ, ht₀, hc₀⟩ hs₀
  have e₁ := eq_mul_of_isTwistPull (c := κ c) A.isLB eth hs₁ hu₁
  have e₂ := eq_mul_of_isTwistPull (c := κ c) A.isLB e₁ ht ht₀
  have h₁ := hlin F (m ^ 2) w₀ t₀ t₀ t s₀ s₀ (c - 1) hs₀ hs₀ fun j => by
    refine (e₂ j).trans ?_
    have : κ c • SecM.ofSec A.A t₀ = κ (c - 1) • SecM.ofSec A.A t₀ + SecM.ofSec A.A t₀ := by
      rw [map_sub, map_one, sub_smul, one_smul, sub_add_cancel]
    exact congrArg (fun q => q.1 j) this
  rw [sub_smul, one_smul, sub_add_cancel] at h₁
  have := NuGe.smul Q hr ((isSmul_iff c s₀ s).2 ((hB₁ t).unique hs h₁)) hP.1
  rwa [zero_add] at this

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocusStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pelTrivialisation_isUnit_on_abelianLocus : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso → IsOpen (abLocus t.G) → ∀ y, PsiUnitOn P.D.toPre y (abLocus t.G) := by
  first | exact @GlobalTheory.psiUnitOn_abLocus_pel | exact GlobalTheory.psiUnitOn_abLocus_pel | (intros; apply GlobalTheory.psiUnitOn_abLocus_pel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsCoordsRelabelledTwistedDataSeriesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoints_coords_relabelled_twistedData_series : GlobalTheory.UT.LL → BrGtSt → TXSt → EVSt → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (I : FullI o) (N N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : N.Form k) (u : Cˣ) (r : ℕ → Cˣ) (J : NumD.Iso (N.twist β u) N') (q : ∀ j : ℕ, D.La → N.QT j), (∀ j, 0 < j → ∀ x, ∃ (q' : N'.QT j) (p' : QkPt M.P.D.toPre C j) (z : TFK (R := M.W) C ⟶ M.P.A.A), TwJ β u (r j) J (q j x) q' ∧ ν'.QPt p' q' ∧ z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j p' z) → ∀ m, Odd m → ∀ p : D.La → (N.twist β u).QT (m ^ 2), (∀ x, TwRel β u (r (m ^ 2)) (q _ x) (p x)) → (withI o I).Theta m (fun x => (N.twist β u).tx m (p x)) ∧ ∀ j, 0 < j → ∀ z (p₀ : (N.twist β u).QT j), TwRel β u (r j) (q j z) p₀ → (withI o I).Coord m (I.ev j z) fun x => (N.twist β u).ev m (p x) p₀.1.2 := by
  first | exact @GlobalTheory.RelabelCoords.theta_coord | exact GlobalTheory.RelabelCoords.theta_coord | (intros; apply GlobalTheory.RelabelCoords.theta_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionCoordinatesEqDegenerationSeriesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionCoordinates_eq_degenerationSeries : HV → BrGtSt → BrFamSt → EVSt := by
  first | exact @GlobalTheory.Ex.CoordSeries.coord_eq_series | exact GlobalTheory.Ex.CoordSeries.coord_eq_series | (intros; apply GlobalTheory.Ex.CoordSeries.coord_eq_series <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionTorsionMemUnitThetaConstantGroupStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_torsion_mem_unitThetaConstantGroup : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ n j : ℕ, n.Prime → Odd n → IsUnit (n : V) → 2 ≤ j → ∀ x : TFK (R := V) F ⟶ A.A, FromGt U.toUnifPre (n ^ j) x → x ∈ unitGrp v ρ th (n ^ j) := by
  first | exact @GlobalTheory.OneBasis.UnitGen.fromGt_mem_unitGrp | exact GlobalTheory.OneBasis.UnitGen.fromGt_mem_unitGrp | (intros; apply GlobalTheory.OneBasis.UnitGen.fromGt_mem_unitGrp <;> assumption)
end

