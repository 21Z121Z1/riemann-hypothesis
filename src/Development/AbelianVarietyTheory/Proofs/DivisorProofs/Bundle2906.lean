import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinGeometricOfSemistableReductionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedIsoPulledBackPeriodRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoTranslateEvenCubicalBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierExponentNonzeroSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.MumMult

theorem exists_closedFibre_pt (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) :
    ∃ x : D.toPre.P.A.left, D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) := by
  let y : (𝟙_ (Over (Sp R))).left := (IsLocalRing.closedPoint R : PrimeSpectrum R)
  refine ⟨(η[D.toPre.P.A]).left y, ?_⟩
  rw [← Scheme.Hom.comp_apply, Over.w (η[D.toPre.P.A])]
  rfl

theorem exists_N_sec : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ N : ℕ, 1 ≤ N ∧ GlobalTheory.MumMult.PosN D a h h' N ∧ ∃ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) ∧ GlobalTheory.MumMult.NonzeroAt D a N σ₀ x := by
  intro R _ _ _ hR D a a' h h' hE
  have := D.toPre.P.isAb.proper
  have hP := D.toPre.P.isLB
  obtain ⟨N₀, hN₀, -, hκ⟩ := GlobalTheory.Mum.PosMult.exists_pos_mult R hR.1 D a a' h h' hE
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.Mum.PosMult.eventually_relAmple R D.toPre.P a
  have hA : IsAmpleLB D.toPre.P.L := isAmpleLB_of_relAmple_of_isAffine D.toPre.P.A hP D.toPre.P.ample
  have hNb := LB.isLB_linComb hP (K := Fin 1) ![a.left] ![1]
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    (GlobalTheory.AmpleDominates.eventually_isGenerated D.toPre.P.A.hom hA hNb)
  set N := max N₀ (max N₁ N₂) with hNdef
  have hN0 : N₀ ≤ N := le_max_left _ _
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  have hL' := LB.isLB_linComb hP (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]
  have hG := hN₂ N hN2
  have hD := LB.isLB_div (isLB_lbPow hP N) hNb
  have hGen : IsGenerated (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]) := by
    refine hG.of_lbIso hL' ((cls_eq_iff hL' hD).1 ?_)
    rw [cls_linComb hP, cls_div (isLB_lbPow hP N) hNb, cls_lbPow hP, cls_linComb hP]
    simp [Fin.sum_univ_two, GlobalTheory.CechPic.pull_id]
    abel
  refine ⟨N, le_trans hN₀ hN0, ⟨hN₁ N hN1, ?_⟩, ?_⟩
  · intro κ hs h0 hc hint hb y
    obtain ⟨r, hr⟩ := hκ κ hs h0 hc hint hb y
    obtain ⟨r', hr'⟩ := hint y
    refine ⟨r' ^ (N - N₀) * r, ?_⟩
    have hsplit : (κ y : FractionRing R) ^ N = (κ y : FractionRing R) ^ (N - N₀) * (κ y : FractionRing R) ^ N₀ := by
      rw [← pow_add, Nat.sub_add_cancel hN0]
    have hr0 : ((κ y ^ N₀ : (FractionRing R)ˣ) : FractionRing R) = (κ y : FractionRing R) ^ N₀ := Units.val_pow_eq_pow_val _ _
    rw [Units.val_pow_eq_pow_val, hsplit, ← hr0, hr, map_mul, map_pow, ← hr']
    ring
  · obtain ⟨x, hx⟩ := exists_closedFibre_pt R D
    obtain ⟨σ₀, hσ⟩ := hGen.exists_mem x
    refine ⟨σ₀, x, hx, fun j hj => ?_⟩
    exact (mem_nonzeroLocus_iff_basicOpen σ₀ hj).1 hσ

end GlobalTheory.MumMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordTermTranslateNormalisedGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.MumTerm

variable {X Y Z : Scheme.{0}}

theorem scal_spec {A B : Type} [CommRing A] [CommRing B] (q : Y ⟶ Sp B) (φ : A →+* B) (r : A) :
    scal q (φ r) = scal (q ≫ Spec.map (CommRingCat.ofHom φ)) r := by
  have e := congrArg (fun h => h.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [e]

theorem gs_scal {A : Type} [CommRing A] (p : Z ⟶ Y) (q : Y ⟶ Sp A) (z : Z) (r : A) :
    gs p z ⊤ (scal q r) = gs (p ≫ q) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) :=
  gs_pull p q z ⊤ trivial _

theorem exists_smul {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) : ∃ t : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval t r z J = gs r z ⊤ a * sval s r z J := by
  refine ⟨⟨fun i => (Y.presheaf.map (homOfLE le_top).op).hom a * s.f i, fun i j => ?_⟩, fun Z r z J hJ => ?_⟩
  · rw [map_mul, map_mul, s.compat i j, mul_left_comm]
    congr 2
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  · have hm := hJ.mem φ r
    exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a))

theorem exists_term : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X) (N : ℕ) (s₀ : SecT D.toPre a N (-1) 0) (ν : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1)))), u₀.IsGen → ∀ ρ : R, (∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) ρ)) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val) → ∃ t : SecT D.toPre a N (-1) (shift h h' N (-1) ν), TRel h ν s₀ t ∧ ∀ e : ℕ, ρ ∈ maximalIdeal R ^ (e + 1) → Van (maximalIdeal R) t e := by
  intro R _ _ _ D a h h' N s₀ ν u₀ hu₀ ρ H
  obtain ⟨p, hp⟩ := exists_sec D.toPre.P.isLB (φ' := tφ D.toPre a (shift h h' N (-1) ν)) (ε' := tε N (-1))
    (fun U _ g => by
      simp only [Fintype.prod_sum_type, dε, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
    (pullMulSec s₀ (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left u₀ hu₀)
  obtain ⟨t, ht⟩ := exists_smul (scal D.toPre.P.A.hom ρ) p
  refine ⟨t, fun u hu Z x z J hJ => ?_, fun e he Z x z J hJ => ?_⟩
  · have e₁ : (DegPre.prB D.toPre (FractionRing R)).left ≫ (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left =
        (DegPre.trF D.toPre (FractionRing R) ν).left ≫ (DegPre.prB D.toPre (FractionRing R)).left := by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      simp only [DegPre.trF, padd, lift_snd]
      rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
    have e₂ : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom =
        ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left :
          (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) ≫ jK R := by
      have j : jFK (R := R) (FractionRing R) = 𝟙 _ := by
        simp [jFK]
      rw [Over.w]
      refine (Over.w (fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R))).symm.trans ?_
      congr 1
      show jFK (R := R) (FractionRing R) ≫ jK R = jK R
      rw [j, Category.id_comp]
    rw [ht _ _ z J hJ, hp _ _ z J hJ, sval_pullMulSec _ _ _ _ _ z hJ, H u hu Z x z J hJ, Category.assoc, e₁,
      scal_spec, gs_scal, gs_scal, Category.assoc, e₂, mul_left_comm]
  · rw [ht _ _ z J hJ, gs_scal, Category.assoc, pullback.condition, ← gs_scal, ← scal_spec,
      Ideal.Quotient.eq_zero_iff_mem.2 he]
    have : scal (pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (0 : R ⧸ maximalIdeal R ^ (e + 1)) = 0 := by
      simp only [scal, map_zero]
    exact (congrArg (· * _) ((congrArg (gs x z ⊤) this).trans (DVR.gs_zero x z ⊤ trivial))).trans (zero_mul _)

end GlobalTheory.MumTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveToricMinorModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.SiegJoin

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isUnit_of_isHom {X M : RatModel o Ω} {f : M.Z ⟶ X.Z} (hf : X.IsHom M (AlgHom.id o Ω) f) {z : M.Z} {y : Ω}
    (hy : y ∈ X.O (f z)) (hu : IsUnit (⟨y, hf.map_mem_O hy⟩ : M.O z)) : IsUnit (⟨y, hy⟩ : X.O (f z)) := by
  obtain ⟨U, a, hz, rfl⟩ := hy
  rw [RatModel.isUnit_valF_iff hz]
  have hz' : z ∈ f ⁻¹ᵁ U := hz
  have e : (⟨valF X.pt U a, hf.map_mem_O ⟨U, a, hz, rfl⟩⟩ : M.O z) =
      ⟨valF M.pt (f ⁻¹ᵁ U) (f.app U a), RatModel.valF_mem_O hz' _⟩ :=
    Subtype.ext (hf.valF_app ⟨_, hz⟩ a).symm
  rw [e, RatModel.isUnit_valF_iff hz', ← Scheme.preimage_basicOpen] at hu
  exact hu

theorem div_iff_of_isHom {X M : RatModel o Ω} {f : M.Z ⟶ X.Z} (hf : X.IsHom M (AlgHom.id o Ω) f) {J : Type}
    {t : J → Ω} (hX : X.HasDiv t) (z : M.Z) (x : J) : M.Div t x z ↔ X.Div t x (f z) := by
  obtain ⟨i, hi⟩ := hX (f z)
  have hi' : M.Div t i z := hf.div hi
  refine ⟨fun hx => ?_, fun hx => hf.div hx⟩
  rw [hi.div_iff_isUnit]
  exact isUnit_of_isHom hf (hi.2 x) ((hi'.div_iff_isUnit x).1 hx)

end GlobalTheory.SiegJoin

namespace GlobalTheory.SiegJoin

theorem minor_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω → ∃ (X M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (Zh : ZHOut ρ M U₀ EE), MinorAt S X M U₀ EE f Xab ∧ IsOpen (abLocus Zh.G) ∧ (abLocus Zh.G : Set M.Z) = f ⁻¹' (Xab : Set X.Z) := by
  intro o Ω _ _ _ _ S ρ hB hfin
  have hL := GlobalTheory.abelianSchemeLaws_all
  have hT : S.HasTests := (GlobalTheory.T.thetaSystem_hasTests_of_real_point GlobalTheory.T.semistableReduction_ppav_padicField GlobalTheory.T.uniformisationExistence_and_torsion_statements.1 hL.1 hL.2 GlobalTheory.T.uniformisationExistence_and_torsion_statements.2 o Ω S ρ).1
  obtain ⟨n, a, GG, X, M, U₀, EE, f, Xab, hNm, hP, -, hO, hE, hH, hXab, hI, hgen, -⟩ := GlobalTheory.T.exists_normal_model_theta_tuple_maximal_minors o Ω S hT hfin
  obtain ⟨Zh⟩ := GlobalTheory.T.zarhinGeometric_of_semistableReduction GlobalTheory.T.semistableReduction_ppav_padicField o Ω S ρ hB M U₀ EE hO hE ⟨n, a, GG, hgen⟩
  have hsupI : ∀ z : M.Z, S.supI M z = S.supI X (f z) := fun z =>
    Set.ext fun x => div_iff_of_isHom hH hNm.1 z x
  have key : (abLocus Zh.G : Set M.Z) = f ⁻¹' (Xab : Set X.Z) := by
    rw [Zh.ab, hXab]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ThetaSys.TT, ThetaSys.HH, hsupI z]
  refine ⟨X, M, U₀, EE, f, Xab, Zh, ⟨hNm, hP, hNm.isNormalScheme, hO, hE, hH, hXab, hI⟩, ?_, key⟩
  rw [key]
  exact Xab.isOpen.preimage f.continuous

end GlobalTheory.SiegJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedIsoPulledBackPeriodRelationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_iso_pulledBack_period_relation : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → LBIso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∃ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen ∧ IsNormIso w₁ ∧ PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q := by
  first | exact @GlobalTheory.TChart.Ratio.exists_normIso_periodRel | exact GlobalTheory.TChart.Ratio.exists_normIso_periodRel | (intros; apply GlobalTheory.TChart.Ratio.exists_normIso_periodRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTwistedIotaGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam

theorem exists_iota_of_rosati {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a a' : D.P.A ⟶ D.P.A)
    [IsMonHom a] [IsMonHom a'] (hr : RosatiAdj D.P.A D.P.L a a') (α δ : D.X) (hc : D.c δ = D.c α ≫ a') :
    ∃ u : LB.Gen (IotaLB D a α δ), IsIota u := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB a a' hr
  have cf : ∀ T, DVR.cP D T δ = DVR.cP D T α ≫ a' := fun T => by
    rw [DVR.cP, hc, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) δ) (D.Oφ a α)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (DVR.prod_neg _ _ (prod_ros a a' (𝟙 D.P.A) (DVR.cP D _ α) h)).trans (Eq.symm ?_)
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) δ h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D a α h)).trans ?_
      rw [cf, Category.id_comp, _root_.mul_comm (DVR.cP D _ α) a, _root_.mul_comm (DVR.cP D _ α ≫ a') (𝟙 _)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _))
  refine ⟨v, hv, fun Z r z J hJ => ?_⟩
  let T : Over (Spec (CommRingCat.of R)) := Over.mk r
  have C : IsCub (cubV D.cub (T := T) z J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb a a' u hu u₀ (T := T) hJ 1 1 (DVR.cP D _ α)).1
  rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := T) z J 1 (DVR.cP D _ α) = 1 := mul_eq_left.1 e.symm
  have o : (1 : T ⟶ D.P.A).left = r ≫ eSec D.P.A := rfl
  have k : (r ≫ eSec D.P.A) ≫ (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left = (lift (1 : T ⟶ D.P.A) (DVR.cP D T α)).left := by
    rw [← o, ← Over.comp_left, comp_lift, DVR.comp_cP, Category.comp_id]
  rw [vv Z _ z J hJ, val_inv, val_pull hJ, k]
  exact inv_eq_one.2 e'

theorem exists_iota : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ α : D.toPre.X, ∃ u : LB.Gen (IotaLB D.toPre a α (h' α)), IsIota u := by
  intro R _ _ _ _ D a a' h h' hE α
  obtain ⟨h₁, h₂, hr, -, hc, -⟩ := hE
  exact exists_iota_of_rosati D.toPre a a' hr α (h' α) (hc α)

end GlobalTheory.TwFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenFiniteOntoOfLevelCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

theorem exists_openAt_of_levAt : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (β : cycAway n →+* o) (S : ThetaSys o Ω) (u : Sp S.R ⟶ F.X) (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X)
    (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → X.IsHom M (AlgHom.id o Ω) f →
    IsIso (f ∣_ Xab) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → Set.range d ⊆ Xab →
    ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ f ⁻¹' Xab := by
  intro g n F o Ω _ _ _ β S u Y X M q f Xab d hL hf hiso hd hdo hrange
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id]
  have hf' : M.pt ≫ f = X.pt := by simpa [RatModel.IsHom, hid] using hf
  have hd' : Y.pt ≫ d = X.pt := by simpa [RatModel.IsHom, hid] using hd
  set U : M.Z.Opens := f ⁻¹ᵁ d.opensRange with hUdef
  have hUle : U ≤ f ⁻¹ᵁ Xab := fun m hm => hrange hm
  have hopen : IsOpenImmersion (U.ι ≫ f) := by
    have e : U.ι ≫ f = M.Z.homOfLE hUle ≫ (f ∣_ Xab) ≫ Xab.ι := by
      rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
    rw [e]
    infer_instance
  have hrng : Set.range (U.ι ≫ f) = Set.range d := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact m.2
    · rintro ⟨y, rfl⟩
      have hy : d y ∈ Xab := hrange ⟨y, rfl⟩
      obtain ⟨m', hm'⟩ := (f ∣_ Xab).surjective ⟨d y, hy⟩
      have h1 : f ((f ⁻¹ᵁ Xab).ι m') = d y := by
        rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hm']
        rfl
      have h2 : (f ⁻¹ᵁ Xab).ι m' ∈ U := ⟨y, h1.symm⟩
      exact ⟨⟨_, h2⟩, h1⟩
  let e := IsOpenImmersion.isoOfRangeEq (U.ι ≫ f) d hrng
  have he : e.hom ≫ d = U.ι ≫ f := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨-, hfin, hsurj, hs, hpt⟩ := hL
  refine ⟨U, e.hom ≫ q, ⟨?_, inferInstance, inferInstance, ?_, ?_⟩, fun m hm => hUle hm⟩
  · obtain ⟨w⟩ : Nonempty (Sp Ω) := inferInstance
    refine ⟨M.pt w, Y.pt w, ?_⟩
    have h1 : d (Y.pt w) = X.pt w := by rw [← hd']; rfl
    have h2 : f (M.pt w) = X.pt w := by rw [← hf']; rfl
    exact h1.trans h2.symm
  · rw [Category.assoc, hs, ← hd.inducedModelMorphism_comp_structureMap, ← hf.inducedModelMorphism_comp_structureMap]
    simp only [← Category.assoc, he]
  · intro x hx
    have h : x ≫ e.hom = Y.pt := by
      rw [← cancel_mono d, Category.assoc, he, ← Category.assoc, hx, hf', hd']
    rw [← Category.assoc, h, hpt]

end GlobalTheory.SiegTh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionSpecRingOnAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Div.AffChart

open GlobalTheory.Points

theorem exists_openImm_spec_ringOn (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω)
    (W : M.Z.Opens) (hW : IsAffineOpen W) (hne : (W : Set M.Z).Nonempty) :
    ∃ (χ : Sp (M.ringOn W) ⟶ M.Z) (_ : IsOpenImmersion χ), χ.opensRange = W ∧
      spMap (algebraMap (M.ringOn W) Ω) ≫ χ = M.pt := by
  let φ : Γ(M.Z, W) ⟶ CommRingCat.of (M.ringOn W) := (M.sectionsEquiv W hne).toCommRingCatIso.hom
  haveI : IsIso φ := inferInstanceAs (IsIso (M.sectionsEquiv W hne).toCommRingCatIso.hom)
  refine ⟨Spec.map φ ≫ hW.fromSpec, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.opensRange_comp_of_isIso, hW.opensRange_fromSpec]
  · have hp := M.top_le_preimage_pt hne
    have e : φ ≫ CommRingCat.ofHom (algebraMap (M.ringOn W) Ω) = valMap M.pt W hp := by
      ext f
      exact (M.coe_sectionsEquiv W hne f).trans (M.res_apply W hne f).symm
    rw [spMap, ← Category.assoc, ← Spec.map_comp, e, specMap_valMap_fromSpec]

end GlobalTheory.Div.AffChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenThetaNonvanishingDescendedGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_open_theta_descent : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → ∀ (G' : Over S) [GrpObj G'] (E : Emb π G') (N : Near π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → ∀ (L : LB G'.left), E.Theta L → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), β ≫ G.hom = G'.hom ≫ π → IsOpenImmersion i.left → N.u ≫ β = pullback.fst _ _ ≫ i.left → ∃ (θ : L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ k, g ∈ G'.left.basicOpen (θ.f k) := by
  intro R _ _ S π hπ G' _ E N fU l hl hlf L hT G β i hβ hi hu
  obtain ⟨θ, OY, ⟨y₀, hy₀⟩, hθ⟩ := hT
  haveI := E.imm
  obtain ⟨W, hW, hWY⟩ := (E.j.isEmbedding.isInducing.isOpen_iff).1 OY.isOpen
  have hrng := GlobalTheory.T.closedPoint_range_eq_fixedGroup_image R S π G' E
  have e1 : ∀ z, E.H.ι (l z) = N.u z := fun z => by rw [← Scheme.Hom.comp_apply, hl]
  have e2 : ∀ z, E.f (l z) = fU (pullback.fst N.U.hom π z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hlf, Scheme.Hom.comp_apply]
  have e3 : ∀ z, β (N.u z) = i.left (pullback.fst N.U.hom π z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hu, Scheme.Hom.comp_apply]
  have e4 : ∀ x, G.hom (β x) = π (G'.hom x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hβ, Scheme.Hom.comp_apply]
  have hWj : ∀ y, y ∈ OY ↔ E.j y ∈ W := fun y => by
    show y ∈ (OY : Set E.Y.left) ↔ _
    rw [← hWY]; rfl
  refine ⟨θ, ⟨i.left '' (fU ⁻¹' W), i.left.isOpenEmbedding.isOpenMap _ (hW.preimage fU.continuous)⟩, ?_, ?_⟩
  · obtain ⟨g₀, hg₀c, hg₀f⟩ := hrng.2 hπ y₀
    obtain ⟨z, hz⟩ := N.all (E.H.ι g₀) hg₀c
    have hlz : l z = g₀ := E.H.ι.isOpenEmbedding.injective (by rw [e1, hz])
    refine ⟨i.left (pullback.fst N.U.hom π z), ⟨pullback.fst N.U.hom π z, ?_, rfl⟩, ?_⟩
    · show fU (pullback.fst N.U.hom π z) ∈ W
      rw [← e2 z, hlz, hg₀f]
      exact (hWj y₀).1 hy₀
    · rw [← e3, e4, hz]
      exact hg₀c
  · rintro g ⟨w, hw, hwg⟩ hc
    have hc' : π (G'.hom g) = closedPoint R := by rw [← e4]; exact hc
    obtain ⟨z, rfl⟩ := N.all g hc'
    have hzw : pullback.fst N.U.hom π z = w := i.left.isOpenEmbedding.injective (by rw [hwg, ← e3])
    have hc'' : π (G'.hom (E.H.ι (l z))) = closedPoint R := by rw [e1]; exact hc'
    obtain ⟨y, hy⟩ := hrng.1 (l z) hc''
    have hyO : y ∈ OY := (hWj y).2 (by rw [← hy, e2, hzw]; exact hw)
    obtain ⟨k, hk⟩ := hθ (l z) y hyO hc'' hy
    exact ⟨k, by rwa [e1] at hk⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoTranslateEvenCubicalBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orderTwo_translate_even_cubicalBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → GlobalTheory.Mum.SplitClosed G → GlobalTheory.Mum.TwoTorsRat G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ a : Over.mk (jK R) ⟶ G, a * a = 1 ∧ ∀ P₁ : GlobalTheory.UU.CP G, GlobalTheory.GenTransl.IsGenTransl G P.L.L P₁.L.L a → GlobalTheory.Mum.EvenOn P₁ := by
  first | exact @GlobalTheory.EvenTransl.exists_even_of_transl | exact GlobalTheory.EvenTransl.exists_even_of_transl | (intros; apply GlobalTheory.EvenTransl.exists_even_of_transl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodGeneratorOnOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TauOnOpen

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Sp R).Opens}

theorem tauW_isGen (ψW : PsiOn D W) (a b : D.X) : (ψW.tau a b).IsGen :=
  DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (ψW.psi_gen _) (DVR.invGen_isGen _ _ _ _ (ψW.psi_gen _)))
      (DVR.invGen_isGen _ _ _ _ (ψW.psi_gen _)))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.rig_gen _))

theorem val_tauW_generic (ψW : PsiOn D W) (a b : D.X) (lam : (TK R).left ⟶ W.toScheme) (h : lam ≫ W.ι = jK R)
    (z : (TK R).left) (J) (hJ : Good D.P.L z J) : val (ψW.tau a b) lam z J = val (D.tau a b) (𝟙 _) z J := by
  have hW : lam ≫ W.ι = 𝟙 _ ≫ jK R := h.trans (Category.id_comp _).symm
  obtain ⟨mu, l₁, l₂⟩ : ∃ mu : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, mu ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ ∧
      mu ≫ (jK R ∣_ W) = lam :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ hW,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  have vψ : ∀ χ, val (ψW.psi χ) lam z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
    have e := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) mu).trans (val_pull hJ _ _ _))
    rw [l₁, l₂] at e
    exact e
  have vρ : val (D.rigW W) lam z J = val D.rigK (𝟙 _) z J := by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    exact congrArg (fun q => val D.rig q z J) hW
  refine (TauPull.val_tauW ψW lam hJ a b).trans (Eq.trans ?_ (TauPull.val_tau (𝟙 _) hJ a b).symm)
  rw [← vψ, ← vψ, ← vψ, ← vρ]

end GlobalTheory.TauOnOpen

namespace GlobalTheory

theorem exists_tau_onOpen : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (ψW : PsiOn D W) (a b : D.X), ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε), t.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ W.toScheme) (z : Z) J, Good D.P.L z J → val t r z J = val (ψW.tau a b) r z J) ∧ ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ z J, Good D.P.L z J → val t lam z J = val (D.tau a b) (𝟙 _) z J := by
  intro R _ _ D W ψW a b
  obtain ⟨t, ht, hv⟩ : ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε),
      t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TW W).left) (z : Z) (J), Good D.P.L z J →
        val t r z J = val (ψW.tau a b) r z J := by
    refine exists_gen D.P.isLB (fun U _ h => ?_) (ψW.tau a b) (TauOnOpen.tauW_isGen ψW a b)
    have e₁ : (toUnit (TW W) ≫ D.c (a + b)).left = ((toUnit (TW W) ≫ D.c a) * (toUnit (TW W) ≫ D.c b)).left := by
      rw [D.c_add]; exact congrArg (fun q : TW W ⟶ D.P.A => q.left) (MonObj.comp_mul (toUnit (TW W)) (D.c a) (D.c b))
    have e₂ : (toUnit (TW W)).left ≫ eSec D.P.A = (1 : TW W ⟶ D.P.A).left := rfl
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, e₁, e₂]
    simp [lamPts, negε]
  exact ⟨t, ht, hv, fun lam h z J hJ => (hv _ lam z J hJ).trans (TauOnOpen.val_tauW_generic ψW a b lam h z J hJ)⟩

end GlobalTheory
end
end

