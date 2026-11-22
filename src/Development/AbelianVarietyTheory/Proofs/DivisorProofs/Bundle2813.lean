import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2720
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTraitDescentFiniteExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2495
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteResidueCharZeroAvoidingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_finiteResidue_charZero_avoiding : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B] (m : Ideal B) (h : B), m.IsMaximal → h ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : CharZero V) (t : B →+* V), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Finite (IsLocalRing.ResidueField V) ∧ t h ≠ 0 ∧ (IsLocalRing.maximalIdeal V).comap t = m := by
  first | exact @GlobalTheory.exists_trait_finite_residueField_charZero_avoiding | exact GlobalTheory.exists_trait_finite_residueField_charZero_avoiding | (intros; apply GlobalTheory.exists_trait_finite_residueField_charZero_avoiding <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportGeneratorLbPowToAmpleBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transport_generator_lbPow_to_ampleBundle : ∀ (S' Z : Scheme.{0}) (π : S' ⟶ Z) (M : LB Z) (L : LB S') (N : ℕ), M.IsLB → L.IsLB → LBIso (M.pull π) (lbPow L N) → ∃ T : ∀ (A : Scheme.{0}) (a : A ⟶ S'), LB.Gen (L.pull a) → LB.Gen (M.pull (a ≫ π)), (∀ (A : Scheme.{0}) (a : A ⟶ S') (e : LB.Gen (L.pull a)), e.IsGen → (T A a e).IsGen) ∧ ∀ (A A' Y : Scheme.{0}) (a : A ⟶ S') (a' : A' ⟶ S') (e : LB.Gen (L.pull a)) (e' : LB.Gen (L.pull a')) (r : Y ⟶ A) (r' : Y ⟶ A'), e.IsGen → e'.IsGen → r ≫ a = r' ≫ a' → (∀ (z : Y) (J : (Y ⟶ S') → L.ι), Good L z J → val (L := L) (φ := fun _ : PUnit => a) (ε := fun _ => 1) e r z J = val (L := L) (φ := fun _ : PUnit => a') (ε := fun _ => 1) e' r' z J) → ∀ (z : Y) (J : (Y ⟶ Z) → M.ι), Good M z J → val (L := M) (φ := fun _ : PUnit => a ≫ π) (ε := fun _ => 1) (T A a e) r z J = val (L := M) (φ := fun _ : PUnit => a' ≫ π) (ε := fun _ => 1) (T A' a' e') r' z J := by
  first | exact @GlobalTheory.GenTransport.transport | exact GlobalTheory.GenTransport.transport | (intros; apply GlobalTheory.GenTransport.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaValueSubsingletonBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

noncomputable section

namespace GlobalTheory.UPoinc.USum

theorem exists_isTwVal_of_subsingleton : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A), Subsingleton T.left → Odd m → N = m ^ 2 → τ.IsGen → x ^ N = 1 → h ^ m = β ≫ z₀ → ∃ v, IsTwVal P N m θ τ β x h v := by
  intro B P N m T₀ T θ z₀ τ β x h hT hm hN hτ hx hh
  subst hN
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hL := P.isLB
  obtain ⟨α, hα⟩ : ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left]
      ![((m ^ 2 : ℕ) : ℤ), -1]), α.IsGen := by
    rw [Nat.cast_pow]
    exact GlobalTheory.EmbLocal.exists_mulPull hG P m T
  obtain ⟨U, hU⟩ : ∃ U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) T, SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U := by
    rcases isEmpty_or_nonempty T.left with he | ⟨⟨p⟩⟩
    · exact GlobalTheory.GlobalLift.exists_symLift_empty hL (m ^ 2) x
    · obtain ⟨V, hV, H⟩ := GlobalTheory.EmbLocal.exists_symLift_near hG P (k := m ^ 2) hm.pow x hx p
      obtain ⟨θ', hθ'⟩ := H T (𝟙 T) (by
        rintro _ ⟨q, rfl⟩
        rwa [Subsingleton.elim ((𝟙 T : T ⟶ T).left q) p])
      rw [Category.id_comp] at hθ'
      exact ⟨θ', hθ'⟩
  rcases U with ⟨pt, φU, hφU⟩
  obtain rfl : x = pt := hU.pt_eq.symm
  obtain ⟨s, hs⟩ := GlobalTheory.VVRank.exists_isTwistPull P.A (ψ := mulT P.A T m) (m := snd T P.A ^ m) (hm := lift_snd _ _)
    (a := ((m ^ 2 : ℕ) : ℤ)) (b := 1) hL hα (GlobalTheory.VVRank.pullS P.A 1 β θ)
  obtain ⟨σ, hσ⟩ := GlobalTheory.VVRank.exists_isTwistPull P.A (ψ := translT P.A x) (m := translPt P.A x)
    (hm := lift_snd _ _) hL hφU s
  have e₁ : (ptSecT P.A h).left ≫ (snd T P.A).left = h.left := GlobalTheory.ThetaPtMove.ptSecT_snd h
  have e₂ : (ptSecT P.A h).left ≫ (snd T P.A ^ m).left = (h ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, GlobalTheory.ThetaCompare.pt_snd]
  have e₃ : β.left ≫ z₀.left = (h ^ m).left := by rw [← Over.comp_left, hh]
  obtain ⟨τ', hτ', vτ'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hL (φ' := fun _ : Fin 1 => h.left)
    (ε' := fun _ => ((m ^ 2 : ℕ) : ℤ))
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, e₃, zpow_neg, zpow_one]
      group)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A h).left) (LB.pullGen P.L _ _ τ β.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) (DVR.pullGen_isGen _ _ _ _ hτ _))
  obtain ⟨v, hv⟩ := GlobalTheory.ThetaPtExist.exists_isValueAt hL σ h τ' hτ'
  refine ⟨v, α, ⟨x, φU, hφU⟩, hα, hU, fun Z r z J hJ => ?_⟩
  have q1 := GlobalTheory.ThetaPtMove.sv_of_isValueAt hv r z hJ
  have q2 := GlobalTheory.VVRank.sv_of_isTwistPull P.A hσ (r ≫ (ptSecT P.A h).left) z hJ
  have q3 := GlobalTheory.VVRank.sv_of_isTwistPull P.A hs (r ≫ (ptSecT P.A (x * h)).left) z hJ
  have q4 := GlobalTheory.VVRank.sv_pullS P.A 1 β θ (r ≫ (ptSecT P.A ((x * h) ^ m)).left) z hJ
  rw [Category.assoc, GlobalTheory.ThetaCompare.pt_translT] at q2
  rw [Category.assoc, GlobalTheory.ThetaCompare.pt_mulT] at q3
  rw [vτ' Z r z J hJ, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_mul hJ, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ] at q1
  rw [← q1, q2, q3, q4, Units.val_mul, Category.assoc, _root_.mul_assoc]
  rfl

end GlobalTheory.UPoinc.USum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationAlongGroupIsoLbIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

noncomputable section
namespace GlobalTheory.Mum

open GlobalTheory.TorsionFormCompare in

theorem exists_unif_move_iso_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀] (ε : G ≅ G₀), IsMonHom ε.hom → IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ U : Unif (maximalIdeal R) D A₀ G, LBIso U.LG.L (U₀.LG.L.pull ε.hom.left) := by
  intro R _ _ _ hB D A₀ G G₀ _ _ _ _ ε hε hsa U₀
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have he : eSec G ≫ ε.hom.left = 𝟙 _ ≫ eSec G₀ := by
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ε.hom)
  let L' : RigLB G := ⟨U₀.LG.L.pull ε.hom.left, rigPullOf ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig,
    LB.isLB_pull U₀.LG.isLB _,
    GlobalTheory.CubePullLawChecks.rigPullIsGen ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig U₀.LG.isLB U₀.LG.rigGen⟩
  let w : LB.Iso L'.L (U₀.LG.L.pull ε.hom.left) := idIso L'.L
  have hw : RigAlong ε.hom U₀.LG L' w :=
    ⟨idIso_isGen L'.isLB, (maps_iff w _ (fun _ => eSec G₀) _ L'.rig U₀.LG.rig (𝟙 _) _
      (rigPull_le _ _ he U₀.LG.L) (fun _ => rfl)).1 (idIso_maps L')⟩
  obtain ⟨W, hW, hψ⟩ := psiOnExists R (maximalIdeal R) hR D
  obtain ⟨hD, hid⟩ := exists_isIdPull R D.toPre W hW hψ
  obtain ⟨bc, U, -, hb, -, hgen, hU⟩ :=
    exists_unif_move R (maximalIdeal R) D A₀ G₀ G ε hR hsa hε U₀ L' w hw hD
  obtain ⟨-, w', hw', -⟩ := sameUnif_of_isPullUnif R (maximalIdeal R) D A₀ G₀ G ε hD hid bc U₀ U hb hgen hU
  exact ⟨U, w', hw'.1⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationPullbackToPullDegStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_pullback_to_pullDeg : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'),
    AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R'), Function.Injective φ → I.map φ ≤ I' →
    ∀ (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre)
      (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
      IsSemiAbelian G → ∀ (U : Unif I D A G),
      ∃ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (U' : Unif I' D' A' ((Over.pullback (specOf φ)).obj G)),
        IsPullUnif φ hD (Iso.refl _) U U' := by
  first | exact @GlobalTheory.Mum.UnifPull.exists_pull_of_deg | exact GlobalTheory.Mum.UnifPull.exists_pull_of_deg | (intros; apply GlobalTheory.Mum.UnifPull.exists_pull_of_deg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTraitDescentFiniteExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisedTrait_descent_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∀ (A₀ : PolAV (Sp (Kb R))) (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) → (letI := A₀.isAb.comm; GlobalTheory.ZH.HypS A₀.A A₀.L) → GeomIso A₀ A' e₀ (algebraMap (FractionRing W) (Kb W)) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ UniTrait D₁.toPre A := by
  first | exact @GlobalTheory.Mum.ClosureDescent.exists_uniTrait | exact GlobalTheory.Mum.ClosureDescent.exists_uniTrait | (intros; apply GlobalTheory.Mum.ClosureDescent.exists_uniTrait <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentTriangularFactor
section
set_option autoImplicit false

open Matrix
open GlobalTheory.FlagFibre (Low)

namespace GlobalTheory.FlagCell

theorem exists_elim_row {R : Type} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (i : Fin m)
    (h : IsUnit (A.submatrix (Fin.castLE i.2.le) (Fin.castLE i.2.le)).det) :
    ∃ r : Fin m → R, r i = 1 ∧ (∀ k, i < k → r k = 0) ∧ ∀ j, j < i → ∑ k, r k * A k j = 0 := by
  classical
  set c : Fin i → Fin m := Fin.castLE i.2.le with hc
  set B := A.submatrix c c with hB
  set x : Fin i → R := (fun j => A i (c j)) ᵥ* B⁻¹ with hx
  have hxB : x ᵥ* B = fun j => A i (c j) := by
    rw [hx, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ h, Matrix.vecMul_one]
  have hlt : ∀ l, c l < i := fun l => l.2
  refine ⟨Pi.single i 1 - ∑ l, Pi.single (c l) (x l), ?_, ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.single_eq_same, Finset.sum_apply]
    rw [Finset.sum_eq_zero fun l _ => Pi.single_eq_of_ne (hlt l).ne' _, sub_zero]
  · intro k hk
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [Finset.sum_eq_zero fun l _ => Pi.single_eq_of_ne ((hlt l).trans hk).ne' _,
      Pi.single_eq_of_ne hk.ne', sub_zero]
  · intro j hj
    have hj' : c ⟨j, hj⟩ = j := rfl
    have h1 := congrFun hxB ⟨j, hj⟩
    simp only [Matrix.vecMul, dotProduct, hB, Matrix.submatrix_apply, hj'] at h1
    simp only [Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, one_mul]
    rw [h1, sub_self]

theorem exists_lu (R : Type) [CommRing R] (m : ℕ) (A : Matrix (Fin m) (Fin m) R)
    (h : ∀ l : Fin (m + 1), IsUnit (A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det) :
    ∃ (n : Low m → R) (M : Matrix (Fin m) (Fin m) R),
      M.BlockTriangular id ∧ IsUnit M.det ∧ A = uniR n * M := by
  classical
  choose r h1 h0 hA using fun i : Fin m => exists_elim_row A i (h i.castSucc)
  let L : Matrix (Fin m) (Fin m) R := Matrix.of r
  have hL : L.BlockTriangular OrderDual.toDual := fun i k hk => h0 i k hk
  have hdet : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L hL]
    exact Finset.prod_eq_one fun i _ => h1 i
  have hu : IsUnit L.det := hdet ▸ isUnit_one
  have hAu : IsUnit A.det := by simpa using h (Fin.last m)
  letI := L.invertibleOfIsUnitDet hu
  have hLi : L⁻¹.BlockTriangular OrderDual.toDual := Matrix.blockTriangular_inv_of_blockTriangular hL
  have hd : ∀ i, L⁻¹ i i = 1 := by
    intro i
    have := congrFun (congrFun (Matrix.mul_nonsing_inv L hu) i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.one_apply_eq] at this
    · have h2 : L i i = 1 := h1 i
      rwa [h2, one_mul] at this
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [hLi (i := k) (j := i) hk, mul_zero]
      · rw [hL (i := i) (j := k) hk, zero_mul]
    · simp
  refine ⟨fun s => L⁻¹ s.1.1 s.1.2, L * A, fun i j hj => hA i j hj, ?_, ?_⟩
  · rw [Matrix.det_mul]; exact hu.mul hAu
  · have : (uniR fun s : Low m => L⁻¹ s.1.1 s.1.2) = L⁻¹ := by
      ext a b
      rw [uniR_apply]
      split_ifs with hab hab'
      · rfl
      · rw [hab', hd]
      · exact (hLi (i := a) (j := b) (show a < b from lt_of_le_of_ne (not_lt.1 hab) hab')).symm
    rw [this, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hu, Matrix.one_mul]

end GlobalTheory.FlagCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCuspFormPullbackGoodCoverStatement
section
open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_cuspForm_pullback_goodCover : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), ∃! g, g ∈ Y.V (wtZ a n) ∧ Y.Pull f g := by
  first | exact @GlobalTheory.CoverPull.cusp_pullback_existsUnique | exact GlobalTheory.CoverPull.cusp_pullback_existsUnique | (intros; apply GlobalTheory.CoverPull.cusp_pullback_existsUnique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

open GlobalTheory.CechPic

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem exists_isPullBy {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) :
    ∃ (X' : Obj F 𝔠 S') (φ : X'.A.left ⟶ X.A.left), X'.IsPullBy X b φ := by
  letI : GrpObj ((Over.pullback b).obj X.A) := Functor.grpObjObj
  haveI : IsCommMonObj ((Over.pullback b).obj X.A) := Functor.isCommMonObj_obj
  have hg : IsGrpPullback ((Over.pullback b).obj X.A) X.A b (pullback.fst X.A.hom b) := isGrpPullback_pullback X.A b
  obtain ⟨rm', hrm'⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback X.rm hg
  let A' := (Over.pullback b).obj X.A
  let φ₂ : (G2 A').left ⟶ (G2 X.A).left := (lift (pushPt hg.1.w (fst A' A')) (pushPt hg.1.w (snd A' A'))).left
  have hsq : IsSquare (pullback.fst X.A.hom b) φ₂ := by
    constructor
    · change (lift (pushPt hg.1.w (fst A' A')) (pushPt hg.1.w (snd A' A')) ≫ fst X.A X.A).left = _
      rw [lift_fst]; rfl
    · change (lift (pushPt hg.1.w (fst A' A')) (pushPt hg.1.w (snd A' A')) ≫ snd X.A X.A).left = _
      rw [lift_snd]; rfl
  refine ⟨{ A := A'
            ab := GlobalTheory.isAbelianScheme_pullback_obj b X.A X.ab
            dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg.1 X.dim
            rm := rm'
            P := fun c ↦ (X.P c).pull φ₂
            isLB := fun c ↦ pull_isLB (X.isLB c) _
            rig₁ := fun c ↦ (GlobalTheory.T.pullback_square_diagonal_sections_generated X b A' _ hg φ₂ hsq c).1
            rig₂ := fun c ↦ (GlobalTheory.T.pullback_square_diagonal_sections_generated X b A' _ hg φ₂ hsq c).2
            symm := fun c ↦ (GlobalTheory.T.pullback_square_action_bundle_iso X b A' _ hg rm' hrm' φ₂ hsq c c 1).1
            add := fun c c' ↦ (GlobalTheory.T.pullback_square_action_bundle_iso X b A' _ hg rm' hrm' φ₂ hsq c c' 1).2.1
            smul := fun a c ↦ (GlobalTheory.T.pullback_square_action_bundle_iso X b A' _ hg rm' hrm' φ₂ hsq c c a).2.2
            pos := GlobalTheory.T.pullback_square_diagonal_rel_ample X b A' _ hg φ₂ hsq
            ker := GlobalTheory.T.pullback_square_action_sections_generated X b A' _ hg rm' hrm' φ₂ hsq }, pullback.fst X.A.hom b, ⟨hg, hrm', φ₂, hsq, fun c ↦ ?_⟩⟩
  exact (cls_eq_iff (pull_isLB (X.isLB c) φ₂) (pull_isLB (X.isLB c) φ₂)).1 rfl

theorem IsPullBy.comp {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (h' : X''.IsPullBy X' b' ψ) (h : X'.IsPullBy X b φ) : X''.IsPullBy X (b' ≫ b) (ψ ≫ φ) :=
  GlobalTheory.T.isPullBy_comp' h' h

theorem IsPullBy.cancel {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {χ : X''.A.left ⟶ X.A.left}
    (h : X''.IsPullBy X (b' ≫ b) χ) (h' : X'.IsPullBy X b φ) :
    ∃ ψ : X''.A.left ⟶ X'.A.left, X''.IsPullBy X' b' ψ ∧ ψ ≫ φ = χ :=
  GlobalTheory.T.isPullBy_factor_through h h'

theorem IsPullBy.exists_level {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X b φ) {N : ℕ} (α : X.Level N) :
    ∃ α' : X'.Level N, IsLevelPull α' α b := by
  obtain ⟨α', hα'⟩ := GlobalTheory.T.level_structure_pullback_exists h α
  exact ⟨α', φ, h, hα'⟩

theorem exists_isLevelPull {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {N : ℕ} (α : X.Level N) (b : S' ⟶ S) :
    ∃ (X' : Obj F 𝔠 S') (α' : X'.Level N), IsLevelPull α' α b := by
  obtain ⟨X', φ, h⟩ := exists_isPullBy X b
  obtain ⟨α', hα'⟩ := h.exists_level α
  exact ⟨X', α', hα'⟩

variable {R R' : Type} [CommRing R] [CommRing R']

theorem lieCorr_smul {σ : R →+* R'} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) {v : X.Lie} {v' : X'.Lie} (hv : LieCorr σ φ v v')
    (a : 𝓞 F) : LieCorr σ φ (a • v) (a • v') := by
  change (v'.hom ≫ X'.rm.act a).left ≫ φ = spMap (Chart.dualMapR σ) ≫ (v.hom ≫ X.rm.act a).left
  rw [Over.comp_left, Over.comp_left, Category.assoc, h.act a, ← Category.assoc, hv, Category.assoc]

theorem exists_lieEquiv [Algebra R R'] {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap (algebraMap R R')) φ) :
    ∃ e : R' ⊗[R] X.Lie ≃ₗ[R'] X'.Lie, (∀ v v', LieCorr (algebraMap R R') φ v v' ↔ v' = e (1 ⊗ₜ v)) ∧
      ∀ (a : 𝓞 F) (v : X.Lie), e (1 ⊗ₜ (a • v)) = a • e (1 ⊗ₜ v) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.lie_algebra_base_change_iso (R := R) (R' := R') h
  refine ⟨e, he, fun a v ↦ ?_⟩
  exact ((he _ _).1 (lieCorr_smul h ((he v _).2 rfl) a)).symm

theorem IsPullBy.existsUnique_detGen (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) (δ : X.DetGen) :
    ∃! δ' : X'.DetGen, DetCorr σ φ δ.1 δ'.1 := by
  letI := σ.toAlgebra
  obtain ⟨e, he, -⟩ := exists_lieEquiv (R' := R') h
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X
  have key : ∀ δ' : X'.DetOmega, DetCorr σ φ δ.1 δ' ↔ ∀ v : Fin (Module.finrank ℚ F) → X.Lie,
      δ' (fun i ↦ e (1 ⊗ₜ v i)) = algebraMap R R' (δ.1 v) := fun δ' ↦ by
    refine ⟨fun H v ↦ H v _ fun i ↦ (he _ _).2 rfl, fun H v v' hv ↦ ?_⟩
    obtain rfl : v' = fun i ↦ e (1 ⊗ₜ v i) := funext fun i ↦ (he _ _).1 (hv i)
    exact H v
  obtain ⟨δ', ⟨hs, hv⟩, hu⟩ := GlobalTheory.T.exists_unique_base_change_volume_form R R' X.Lie X'.Lie e _ δ.1 δ.2
  refine ⟨⟨δ', hs⟩, (key δ').2 hv, fun δ'' hδ'' ↦ Subtype.ext (hu δ''.1 ⟨δ''.2, (key δ''.1).1 hδ''⟩)⟩

theorem invertible_detOmega (X : Obj F 𝔠 (Sp R)) : Module.Invertible R X.DetOmega := by
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X
  exact GlobalTheory.T.top_exterior_dual_invertible R X.Lie _ hrk

theorem IsPullBy.isRapoport (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) (hX : X.IsRapoport) : X'.IsRapoport := by
  letI := σ.toAlgebra
  obtain ⟨e, -, he⟩ := exists_lieEquiv (R' := R') h
  exact GlobalTheory.T.base_change_module_tensor_action R R' (𝓞 F) X.Lie X'.Lie e he hX

theorem isRapoport_iff (X : Obj F 𝔠 (Sp R)) : X.IsRapoport ↔ X.rapLocus = Set.univ := by
  constructor
  · intro hX
    refine Set.eq_univ_of_forall fun s K _ t _ Y φ hY ↦ ?_
    obtain ⟨σ, rfl⟩ : ∃ σ : R →+* K, spMap σ = t := ⟨(Spec.preimage t).hom, Spec.map_preimage t⟩
    exact hY.isRapoport σ hX
  · intro hX
    obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X
    refine GlobalTheory.T.module_action_of_field_fibres R (𝓞 F) X.Lie fun K _ _ ↦ ?_
    obtain ⟨Y, φ, hY⟩ := exists_isPullBy X (spMap (algebraMap R K))
    obtain ⟨x⟩ : Nonempty (Sp K) := inferInstance
    have hYr : Y.IsRapoport := (hX ▸ Set.mem_univ (spMap (algebraMap R K) x) : _ ∈ X.rapLocus) K _ ⟨x, rfl⟩ Y φ hY
    obtain ⟨e, -, he⟩ := exists_lieEquiv (R' := K) hY
    exact ⟨Y.Lie, _, _, _, _, e, he, hYr⟩

theorem pullback_facts :
    (∀ {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S), ∃ (X' : Obj F 𝔠 S') (φ : X'.A.left ⟶ X.A.left),
      X'.IsPullBy X b φ) ∧
    (∀ {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
      {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left},
      X''.IsPullBy X' b' ψ → X'.IsPullBy X b φ → X''.IsPullBy X (b' ≫ b) (ψ ≫ φ)) ∧
    (∀ {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
      {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {χ : X''.A.left ⟶ X.A.left},
      X''.IsPullBy X (b' ≫ b) χ → X'.IsPullBy X b φ →
      ∃ ψ : X''.A.left ⟶ X'.A.left, X''.IsPullBy X' b' ψ ∧ ψ ≫ φ = χ) ∧
    (∀ {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S} {φ : X'.A.left ⟶ X.A.left},
      X'.IsPullBy X b φ → ∀ {N : ℕ} (α : X.Level N), ∃ α' : X'.Level N, IsLevelPull α' α b) ∧
    (∀ {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
      {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap σ) φ →
      (∀ δ : X.DetGen, ∃! δ' : X'.DetGen, DetCorr σ φ δ.1 δ'.1) ∧ Module.Invertible R X.DetOmega ∧
        (X.IsRapoport → X'.IsRapoport)) ∧
    (∀ {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport ↔ X.rapLocus = Set.univ) :=
  ⟨exists_isPullBy, fun h' h ↦ h'.comp h, fun h h' ↦ h.cancel h', fun h _ α ↦ h.exists_level α,
    fun σ _ _ _ h ↦ ⟨h.existsUnique_detGen σ, invertible_detOmega _, h.isRapoport σ⟩, isRapoport_iff⟩

end GlobalTheory.RealMult.Obj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueExtendPointAbelianSchemeDVRStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_extend_point_abelianScheme_DVR : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (x : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ P.A), ∃! y : Over.mk (spMap f) ⟶ P.A, spMap (algebraMap W L) ≫ y.left = x.left := by
  first | exact @GlobalTheory.DVRExt.exists_unique_extend | exact GlobalTheory.DVRExt.exists_unique_extend | (intros; apply GlobalTheory.DVRExt.exists_unique_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem IntFam.existsUnique_over : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ)
    (F₀ : IntFam I D k) (F : Type) [Field F] [Algebra (FractionRing R) F], ∃! s : Fam D F k, F₀.Over s := by
  intro R _ _ I D k F₀ F _ _
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hL := D.P.isLB
  have hext : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F₀.F.s α)
      (D.famφB α) (DegPre.famε k) (F₀.f α) (DegPre.prB D (FractionRing R)).left 1 := fun α => by
    have h := F₀.ext α
    have e : scal (DegPre.BF D (FractionRing R)).hom (1 : R) = 1 := by
      unfold scal
      rw [map_one, map_one]
    rwa [e] at h
  have hov : F₀.Over (famPull D (FractionRing R) F hG k F₀.F) := fun α => by
    refine SectionScalarValuation.secScal_of_sval hL fun y J hJ => ?_
    show _ = sval (termPull D (FractionRing R) F k α (F₀.F.s α)) (𝟙 _) y J
    refine Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm
    refine Eq.trans ?_ (SectionScalarValuation.secScal_sval (hext α) _ y hJ)
    congr 1
    rw [Category.assoc, ← Over.comp_left, famMap_snd]
  refine ⟨_, hov, fun s hs => fam_ext fun α j => congrArg (fun q => LB.Sec.f q j)
    (sec_ext' hL fun y J hJ => ?_)⟩
  rw [← SectionScalarValuation.secScal_sval (hs α) (𝟙 _) y hJ, SectionScalarValuation.secScal_sval (hov α) (𝟙 _) y hJ]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGlueMapsOpenCoverSameSourceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_glue_maps_openCover_same_source : ∀ (X Y P : Scheme.{0}) (J : Type) (e : J → (P ⟶ X)) (g : J → (P ⟶ Y)), (∀ j, IsOpenImmersion (e j)) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ P), a ≫ e i = b ≫ e j → a ≫ g i = b ≫ g j) → ∃ β : X ⟶ Y, (∀ j, e j ≫ β = g j) ∧ ∀ β' : X ⟶ Y, (∀ j, e j ≫ β' = g j) → β' = β := by
  first | exact @GlobalTheory.GlueDesc.exists_unique_glue | exact GlobalTheory.GlueDesc.exists_unique_glue | (intros; apply GlobalTheory.GlueDesc.exists_unique_glue <;> assumption)
end

