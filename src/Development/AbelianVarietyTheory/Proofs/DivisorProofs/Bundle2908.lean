import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.QkExtExistsG
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2836
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProperNormalFlagSchemeOfAffineCoverStatement
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_proper_normal_flagScheme_of_affine_cover : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover (RingHom.id K) s V α c D → (∀ x : X, ∃ b, x ∈ (V b).1) → ∃ (Z : Scheme.{0}) (π : Z ⟶ X) (g : ∀ en : En m, Z ⟶ PSpace K (plN M en.1)) (κ : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ Z)), IsProper π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧ HasPlk (RingHom.id K) V α c π g κ ∧ (∀ b w, IsOpenImmersion (κ b w)) ∧ (∀ z : Z, ∃ b w, z ∈ Set.range (κ b w)) ∧ ∀ (W : Scheme.{0}) (a a' : W ⟶ Z), a ≫ π = a' ≫ π → (∀ en, a ≫ g en = a' ≫ g en) → a = a' := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.exists_properFlag | exact GlobalTheory.FlagMod.FieldFlag.exists_properFlag | (intros; apply GlobalTheory.FlagMod.FieldFlag.exists_properFlag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackTwistedSectionVanishing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem formEq_pull {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k : ℕ) (α δ : D.X) :
    FormEq (Sum.elim (fun i => a.left ≫ D.famφB α i) (Sum.elim (D.Oφ (𝟙 D.P.A) δ) (D.Oφ a α)))
      (Sum.elim (DegPre.famε k) (Sum.elim Oε Oinvε)) (tφ D a δ) (tε 0 k) := by
  intro U _ h
  have e₁ : a.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = (padd D.P.A a (toUnit _ ≫ D.c α)).left := by
    rw [← Over.comp_left, padd, padd, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  have e₂ : a.left ≫ (toUnit D.P.A ≫ D.c α).left = (toUnit D.P.A ≫ D.c α).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  have e₃ : a.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (toUnit D.P.A ≫ η[D.P.A]).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, DegPre.famφB,
    DegPre.Oφ, tφ, tε, DegPre.famε, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_succ, e₁, e₂, e₃,
    Category.comp_id, Over.id_left]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_one]
  module

theorem exists_isPullT : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (k : ℕ) (α δ : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α δ)) (f : D.toPre.SecB k α), u.IsGen → ∃ s : SecT D.toPre a 0 k δ, IsPullT u f s ∧ ∀ e, VanMod (maximalIdeal R) f e → Van (maximalIdeal R) s e := by
  intro R _ _ _ _ D a k α δ u f hu
  obtain ⟨s, hs⟩ := exists_sec D.toPre.P.isLB (formEq_pull D.toPre a k α δ) (pullMulSec f a.left u hu)
  have hp : IsPullT u f s := fun Z x z J hJ => (hs Z x z J hJ).trans (sval_pullMulSec f a.left u hu x z hJ)
  refine ⟨s, hp, fun e hb Z x z J hJ => ?_⟩
  obtain ⟨h, hh⟩ : ∃ h : Z ⟶ pullback D.toPre.P.A.hom (thick R (maximalIdeal R) e),
      h ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
        (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ a.left :=
    ⟨pullback.lift _ (x ≫ pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (by
      rw [Category.assoc, Over.w, Category.assoc, Category.assoc, pullback.condition]), pullback.lift_fst _ _ _⟩
  have z₁ : sval f ((x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ a.left) z J = 0 := by
    rw [← hh]
    have hm := hJ.mem (D.toPre.famφB α) (h ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e))
    exact (gs_pull h _ z _ hm _).symm.trans ((congrArg (gs h z _) (hb _)).trans (DVR.gs_zero h z _ hm))
  rw [hp Z _ z J hJ, z₁, zero_mul]

end GlobalTheory.TwFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorSectionEveryPointStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pushoutTorsorSection_every_point : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ s : RootFn A D, IsSec n b x s := by
  first | exact @GlobalTheory.PtExt.PushSec.exists_isSec | exact GlobalTheory.PtExt.PushSec.exists_isSec | (intros; apply GlobalTheory.PtExt.PushSec.exists_isSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQkZeroOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem exists_qk_zero_over : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
    ∀ b : TF (R := V) F ⟶ D.P.A, b ^ k = 1 → ∃ p : QkPt D F k, p.y = 0 ∧ p.g.b = b := by
  intro V _ _ D hB F _ _ _ k hk b hb
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F)
  exact exists_qk_over (F := F) hJ hB hk 0 b (by rw [hb, cPoint_zero])

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalTatePairsUnitaryType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TraitTate

open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem exists_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V), Function.Injective b → ∀ (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), PelOK Dm D.toPre o → (∀ k : ℕ, k ∣ l.M' → ∀ q : QkPt D.toPre (AlgebraicClosure (FractionRing T.V)) k, ∃ p : QkPt D.toPre (FractionRing T.V) k, QkExt (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) p q) → ∃ (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M), ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A → ∃ I : (letI := H.starRing; TateIsoQ Dm D.toPre o F), (I.ζ l.A : F) = algebraMap (FractionRing T.V) F (algebraMap T.V _ (b z)) ∧ (∀ a q, QkExt (algebraMap _ F) (pA a) q → QkPt.Equiv D.toPre F q (I.ev l.A a)) ∧ ∀ a q, QkExt (algebraMap _ F) (pM a) q → QkPt.Equiv D.toPre F q (I.ev l.M a) := by
  intro E _ _ _ H Dm l c O _ β hβ T b hb D _ o hP hrat
  letI := H.starRing
  haveI : CharZero (FractionRing T.V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective T.V (FractionRing T.V))
  haveI : CharZero (AlgebraicClosure (FractionRing T.V)) :=
    charZero_of_injective_algebraMap (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))).injective
  have hB : D.toPre.TauBimult := D.tau_bimult

  set g : O →+* AlgebraicClosure (FractionRing T.V) :=
    (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))).comp ((algebraMap T.V _).comp b) with hg
  have hginj : Function.Injective g :=
    (algebraMap (FractionRing T.V) _).injective.comp ((IsFractionRing.injective T.V (FractionRing T.V)).comp hb)

  obtain ⟨ζ₀, hζp, hζc, hζA⟩ : ∃ ζ₀ : ℕ → (AlgebraicClosure (FractionRing T.V))ˣ,
      (∀ n, 0 < n → IsPrimitiveRoot (ζ₀ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ₀ (n * m) ^ m = ζ₀ n) ∧
      ∀ z : O, ((β z : c.F) : ℂ) = zeta l.A → (ζ₀ l.A : AlgebraicClosure (FractionRing T.V)) = g z := by
    by_cases hz : ∃ z : O, ((β z : c.F) : ℂ) = zeta l.A
    · obtain ⟨z, hz⟩ := hz
      have h₀ : IsPrimitiveRoot (((β z : c.F) : ℂ)) l.A := by
        rw [hz]; exact Complex.isPrimitiveRoot_exp l.A l.A_pos.ne'
      have h₁ : IsPrimitiveRoot (β z) l.A :=
        IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) h₀ Subtype.val_injective
      have h₂ : IsPrimitiveRoot z l.A := IsPrimitiveRoot.of_map_of_injective (f := β) h₁ hβ
      have h₃ : IsPrimitiveRoot (g z) l.A := h₂.map_of_injective hginj
      obtain ⟨ζ, e₁, e₂, e₃⟩ := GlobalTheory.T.exists_compatible_primitiveRoots_through (AlgebraicClosure (FractionRing T.V)) l.A (g z) l.A_pos h₃
      refine ⟨ζ, e₁, e₂, fun z' hz' => ?_⟩
      have : z' = z := hβ (Subtype.val_injective (hz'.trans hz.symm))
      rw [this]; exact e₃
    · obtain ⟨ζ, e₁, e₂, -⟩ := GlobalTheory.T.exists_compatible_primitiveRoots_through (AlgebraicClosure (FractionRing T.V)) 1 1 one_pos IsPrimitiveRoot.one
      exact ⟨ζ, e₁, e₂, fun z hz' => (hz ⟨z, hz'⟩).elim⟩

  obtain ⟨-, -, -, hF⟩ := hP
  obtain ⟨-, hT⟩ := hF (AlgebraicClosure (FractionRing T.V))
  obtain ⟨I₀, hI₀⟩ := hT ζ₀ hζp hζc

  have hA : l.A ∣ l.M' := Nat.dvd_lcm_right l.M l.A
  have hM : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
  choose pA hpA using fun a => hrat l.A hA (I₀.ev l.A a)
  choose pM hpM using fun a => hrat l.M hM (I₀.ev l.M a)
  refine ⟨pA, pM, fun F _ _ _ z hz => ?_⟩

  let e : AlgebraicClosure (FractionRing T.V) →ₐ[FractionRing T.V] F :=
    IsAlgClosed.lift (M := F) (R := FractionRing T.V) (S := AlgebraicClosure (FractionRing T.V))
  have he : (e : AlgebraicClosure (FractionRing T.V) →+* F).comp
      (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) = algebraMap (FractionRing T.V) F :=
    RingHom.ext fun x => e.commutes x
  have hK : (algebraMap (AlgebraicClosure (FractionRing T.V)) (AlgebraicClosure (FractionRing T.V))).comp
      (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) =
      algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V)) := RingHom.ext fun _ => rfl

  have base : ∀ {k : ℕ} (p₀ : QkPt D.toPre (FractionRing T.V) k) (r : QkPt D.toPre (AlgebraicClosure (FractionRing T.V)) k),
      QkExt (algebraMap _ (AlgebraicClosure (FractionRing T.V))) p₀ r →
      ∀ p, QkExt (algebraMap _ (AlgebraicClosure (FractionRing T.V))) p₀ p →
        QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing T.V)) p r := by
    intro k p₀ r hr p hp
    have u := (existsUnique_qkExt hB (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) hK p₀).unique hp hr
    rw [u]; exact qk_equiv_refl hB r
  refine ⟨tateExt (e : AlgebraicClosure (FractionRing T.V) →+* F) he hB abelianSchemeLaws_all.1 I₀
    (ArcInputCompare.weil_ext hB (e : AlgebraicClosure (FractionRing T.V) →+* F) he), ?_, ?_, ?_⟩
  ·
    show ((Units.map (e : AlgebraicClosure (FractionRing T.V) →+* F).toMonoidHom (I₀.ζ l.A) : Fˣ) : F) = _
    rw [hI₀, Units.coe_map, hζA z hz, hg]
    exact e.commutes _
  · intro a q hq
    exact GlobalTheory.LiftExt.equiv_of_base hB _ he (base (pA a) _ (hpA a)) q hq
  · intro a q hq
    exact GlobalTheory.LiftExt.equiv_of_base hB _ he (base (pM a) _ (hpM a)) q hq

end GlobalTheory.TraitTate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionDifferentialsInvariantOneFormsAf
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.InvForm

namespace GlobalTheory.InvFormRetract

theorem dVal_smul {R B D : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing D] [Algebra R D] (φ : B →ₐ[R] DualNumber D) (b : B) (x : Ω[B⁄R]) : dVal φ (b • x) = redHom φ b * dVal φ x := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  unfold dVal
  simp only [LinearMap.restrictScalars_apply, LinearMap.map_smul]
  rfl

theorem injective_baseChange {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (hab : IsAbelianScheme A) (U : AffOp A.left) :
    Function.Injective (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype)) := by
  haveI : Smooth A.hom := hab.smooth
  haveI : IsProper A.hom := hab.proper
  haveI : CompactSpace A.left := ⟨by simpa using QuasiCompact.isCompact_preimage (f := A.hom) Set.univ isOpen_univ isCompact_univ⟩
  haveI : Algebra.Smooth R (Sec A.hom U.unop.1) := smooth_sec_affine A.hom U.unop
  haveI : Module.Flat R (Sec A.hom U.unop.1) := Algebra.Smooth.flat R _
  obtain ⟨n, V, hV⟩ := GlobalTheory.T.exists_finite_affineCover_globalForm_eq_zero_of_restrictions R A.left A.hom inferInstance
  let f : ∀ k, InvForm A →ₗ[R] Ω[Sec A.hom (V k).unop.1⁄R] := fun k => evForm A.hom (V k) ∘ₗ (InvForm A).subtype
  let F : InvForm A →ₗ[R] ((k : Fin n) → Ω[Sec A.hom (V k).unop.1⁄R]) := LinearMap.pi f
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hV w.1 fun k => congrFun hw k)
  have hFB : Function.Injective (LinearMap.lTensor (Sec A.hom U.unop.1) F) :=
    Module.Flat.lTensor_preserves_injective_linearMap F hF
  have hk : ∀ (k : Fin n) (z : Sec A.hom U.unop.1 ⊗[R] InvForm A), TensorProduct.piRight R R (Sec A.hom U.unop.1) (fun k : Fin n => Ω[Sec A.hom (V k).unop.1⁄R])
      (LinearMap.lTensor (Sec A.hom U.unop.1) F z) k = LinearMap.lTensor (Sec A.hom U.unop.1) (f k) z := by
    intro k z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b w => simp [F]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  apply hFB
  rw [map_zero]
  apply (TensorProduct.piRight R R (Sec A.hom U.unop.1) (fun k : Fin n => Ω[Sec A.hom (V k).unop.1⁄R])).injective
  rw [map_zero]
  funext k
  rw [hk, Pi.zero_apply]
  haveI : Algebra.Smooth R (Sec A.hom (V k).unop.1) := smooth_sec_affine A.hom (V k).unop
  refine GlobalTheory.T.eq_zero_of_liftBaseChange_derivations_eq_zero R (Sec A.hom U.unop.1) _ inferInstance _ (fun θ hθ => ?_)
  obtain ⟨ψ, hfst, hψ⟩ := GlobalTheory.T.exists_groupLawTranslate_derivation_invariantForms R A U (V k) θ hθ
  have key : ∀ y, LinearMap.liftBaseChange (Sec A.hom U.unop.1) θ (LinearMap.lTensor (Sec A.hom U.unop.1) (f k) y) =
      dVal ψ (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, dVal_smul]
      have h1 : redHom ψ b = b ⊗ₜ 1 := hfst b
      rw [h1, Algebra.smul_def]
      simp only [f, LinearMap.comp_apply, Submodule.subtype_apply, hψ]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [key, hz, map_zero]

theorem retract : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, ∃ r : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] (Sec A.hom U.unop.1 ⊗[R] GlobalTheory.InvForm.InvForm A), ∀ w : GlobalTheory.InvForm.InvForm A, r (evForm A.hom U w.1) = 1 ⊗ₜ w := by
  intro R _ A _ g hab hdim U
  have hsurj : Function.Surjective (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← GlobalTheory.T.span_invariantOneForms_affineOpen_abelianScheme_eq_top R A g hab hdim U, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨1 ⊗ₜ w, by simp⟩
  let e := LinearEquiv.ofBijective _ ⟨injective_baseChange A hab U, hsurj⟩
  refine ⟨e.symm.toLinearMap, fun w => ?_⟩
  apply e.injective
  rw [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  change _ = LinearMap.liftBaseChange _ _ (1 ⊗ₜ w)
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end GlobalTheory.InvFormRetract
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidificationMatchingFramesTorsionFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
open Classical

namespace GlobalTheory.Poinc.IntTerm

theorem exists_rig_torsFrame_of_match : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∃ ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A)), ρA.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x fr hx hfr
  have gp := 𝔪.cart
  have hw := 𝔪.wl_gen
  obtain ⟨rig', hrig', Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) hw X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm gp) X₁.ρ.rig X₁.ρ.rig_gen
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over _)).left) (z : Z) J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      GlobalTheory.FrameMove.rval X₁.ρ.rig (r ≫ spMap 𝔪.yK) z J = GlobalTheory.ConstFam.wVal 𝔪.wl z J J' (r ≫ eSec 𝔪.A.A) * GlobalTheory.FrameMove.rval rig' r z J' :=
    fun Z r z J J' hJ hJ' =>
      (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  refine ⟨rig', hrig', fun a => ?_⟩
  exact GlobalTheory.FrameMove.isTorsFrame_move gp hw hr (hx a) (X₁.ρ.fr_tors a) (hfr a).1
    (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)

end GlobalTheory.Poinc.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedValueAtOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OrigValExists

theorem mem_of_closed {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : Sp R ⟶ X) (U : X.Opens)
    (h : f (closedPoint R) ∈ U) (z : Sp R) : f z ∈ U := by
  have : f ⁻¹ᵁ U = ⊤ := (closedPoint_mem_iff (f ⁻¹ᵁ U)).1 h
  show z ∈ f ⁻¹ᵁ U
  rw [this]; trivial

theorem exists_stalkOf {R : Type} [CommRing R] {X : Scheme.{0}} (f : Sp R ⟶ X) (U : X.Opens)
    (h : ∀ z, f z ∈ U) (a : Γ(X, U)) : ∃ r : R, ∀ z, gs f z U a = stalkOf z r := by
  have hle : (⊤ : (Sp R).Opens) ≤ f ⁻¹ᵁ U := fun z _ => h z
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Sp R).presheaf.map (homOfLE hle).op).hom ((f.app U).hom a)), fun z => ?_⟩
  rw [gs_eq f z U (h z)]
  have e : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x :=
    fun x => (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply x
  refine Eq.trans ?_ (congrArg ((Sp R).presheaf.germ ⊤ z trivial).hom (e _)).symm
  exact (TopCat.Presheaf.germ_res_apply (Sp R).presheaf (homOfLE hle) z trivial _).symm

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (α : D.X)

theorem unit_fam_zero : unitW D.P.A ≫ D.famφB α 0 = idW R ≫ eSec D.P.A :=
  (Category.comp_id _).trans (Category.id_comp _).symm

theorem unit_fam_one : unitW D.P.A ≫ D.famφB α 1 = unitW D.P.A ≫ D.famφB α 2 := by
  change η[D.P.A].left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = η[D.P.A].left ≫ (toUnit D.P.A ≫ D.c α).left
  rw [← Over.comp_left, ← Over.comp_left]; congr 1
  simp only [padd, comp_lift_assoc, Category.comp_id]
  have := MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over (Sp R)))) (η[D.P.A] ≫ toUnit D.P.A ≫ D.c α)
  rwa [Category.id_comp] at this

theorem unit_fam_three : unitW D.P.A ≫ D.famφB α 3 = idW R ≫ eSec D.P.A := by
  refine Eq.trans ?_ (Category.id_comp _).symm
  change η[D.P.A].left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = η[D.P.A].left
  rw [← Over.comp_left]; congr 1
  rw [← Category.assoc, Subsingleton.elim (η[D.P.A] ≫ toUnit D.P.A) (𝟙 _), Category.id_comp]

theorem trF_unit (k : ℕ) (z : Sp R) (J I : (Sp R ⟶ D.P.A.left) → D.P.L.ι) :
    trF (L := D.P.L) (D.famφB α) (DegPre.famε k) (unitW D.P.A) z (fun i => J (unitW D.P.A ≫ D.famφB α i))
      (fun i => I (unitW D.P.A ≫ D.famφB α i)) =
    trF (L := D.P.L) (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) (idW R) z (fun _ => J (idW R ≫ eSec D.P.A))
      (fun _ => I (idW R ≫ eSec D.P.A)) ^ k := by
  let h : (Sp R ⟶ D.P.A.left) → ((Sp R).presheaf.stalk z)ˣ :=
    fun ψ => gm ψ z (D.P.L.U (J ψ) ⊓ D.P.L.U (I ψ)) (D.P.L.g (J ψ) (I ψ))
  show ∏ i, h (unitW D.P.A ≫ D.famφB α i) ^ DegPre.famε k i = (∏ _i : PUnit, h (idW R ≫ eSec D.P.A) ^ (1 : ℤ)) ^ k
  rw [Fin.prod_univ_four, unit_fam_zero, unit_fam_one, unit_fam_three, Fintype.prod_unique]
  generalize h (idW R ≫ eSec D.P.A) = A
  generalize h (unitW D.P.A ≫ D.famφB α 2) = B
  show A ^ ((k : ℤ) - 1) * B ^ (1 : ℤ) * B ^ (-1 : ℤ) * A ^ (1 : ℤ) = (A ^ (1 : ℤ)) ^ k
  rw [zpow_sub_one, zpow_natCast, zpow_neg, zpow_one, zpow_one, mul_inv_cancel_right, inv_mul_cancel_right]

end GlobalTheory.Mum.OrigValExists

namespace GlobalTheory.Mum
open OrigValExists

theorem exists_origVal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α), ∃ v : R, OrigVal D b v := by
  intro R _ _ _ D k α b
  obtain ⟨I, hI₀, -⟩ := exists_good D.P.L D.P.isLB (Z := Sp R) (closedPoint R) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hI : ∀ z, Good D.P.L z I := fun z ψ => mem_of_closed ψ _ (hI₀ ψ) z
  obtain ⟨a, ha⟩ := exists_stalkOf (unitW D.P.A) _ (fun z => (hI z).mem (D.famφB α) (unitW D.P.A))
    (b.f (fun i => I (unitW D.P.A ≫ D.famφB α i)))
  obtain ⟨u, hu⟩ := exists_stalkOf (idW R) _ (fun z => (hI z).mem (K := PUnit) (fun _ => eSec D.P.A) (idW R))
    ((D.rig.s (fun _ => I (idW R ≫ eSec D.P.A)))⁻¹).val
  refine ⟨a * u ^ k, fun z J hJ => ?_⟩
  have e₁ : sval b (unitW D.P.A) z J = _ * sval b (unitW D.P.A) z I :=
    sec_trans b (unitW D.P.A) z (hJ.mem _ _) ((hI z).mem _ _)
  have e₂ : val D.rig (idW R) z J = _ * val D.rig (idW R) z I :=
    gen_trans D.rig_gen (idW R) z (hJ.mem _ _) ((hI z).mem _ _)
  have e₃ : sval b (unitW D.P.A) z I = stalkOf z a := ha z
  have e₄ : stalkOf z u = ((val D.rig (idW R) z I)⁻¹).val :=
    (hu z).symm.trans ((gs_unit (idW R) z _ ((hI z).mem (K := PUnit) (fun _ => eSec D.P.A) (idW R)) _).trans
      (congrArg Units.val (map_inv _ _)))
  rw [e₁, e₂, e₃, trF_unit, map_mul, map_pow, e₄]
  generalize trF (K := PUnit) _ _ _ _ _ _ = A
  generalize val D.rig (idW R) z I = B
  rw [_root_.mul_assoc, ← mul_pow, ← Units.val_mul, _root_.mul_comm A B, inv_mul_cancel_left, Units.val_pow_eq_pow_val, _root_.mul_comm]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingElementOfLocalFieldPointValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ring_element_of_local_field_point_values : ∀ (R : Type) [CommRing R] (P : (K : Type) → [Field K] → (R →+* K) → K → Prop), (∀ (K : Type) [Field K] (i : R →+* K) (u v : K), P K i u → P K i v → u = v) → (∀ p : Ideal R, p.IsPrime → ∃ f ∉ p, ∃ c : Localization.Away f, ∀ (K : Type) [Field K] (j : Localization.Away f →+* K), P K (j.comp (algebraMap R (Localization.Away f))) (j c)) → ∃ c : R, ∀ (K : Type) [Field K] (i : R →+* K), P K i (i c) := by
  first | exact @GlobalTheory.glue_field_points | exact GlobalTheory.glue_field_points | (intros; apply GlobalTheory.glue_field_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfGeneric
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical
open CategoryTheory.Limits
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlagGenFib
variable {D : D7} {Bs Y₀ : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (π₀ : Y₀ ⟶ Bs)

def Gf : Scheme.{0} := pullback (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))

def jf : Gf q π₀ ⟶ Y₀ := pullback.fst _ _

def sf : Gf q π₀ ⟶ Sp D.what₂.LL := pullback.snd _ _

theorem isPullback_f :
    IsPullback (jf q π₀) (sf q π₀) (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) :=
  IsPullback.of_hasPullback _ _

def jGf {Bg : Scheme.{0}} (jB : Bg ⟶ Bs) (p : Bg ⟶ Sp D.what₂.LL)
    (hB : IsPullback jB p q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) : Gf q π₀ ⟶ Bg :=
  hB.lift (jf q π₀ ≫ π₀) (sf q π₀) (by
    simpa [Category.assoc] using (isPullback_f q π₀).w)

theorem jGf_jB {Bg : Scheme.{0}} (jB : Bg ⟶ Bs) (p : Bg ⟶ Sp D.what₂.LL)
    (hB : IsPullback jB p q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) :
    jGf q π₀ jB p hB ≫ jB = jf q π₀ ≫ π₀ :=
  hB.lift_fst _ _ _

theorem exists_ringHom_of_generic {G X : Scheme.{0}} [IsIntegral G] [IsIntegral X] (f : G ⟶ X)
    (hf : f (genericPoint G) = genericPoint X) :
    ∃ φ : X.functionField →+* G.functionField,
      G.fromSpecStalk (genericPoint G) ≫ f = spMap φ ≫ X.fromSpecStalk (genericPoint X) := by
  have h : f (genericPoint G) ⤳ genericPoint X := by rw [hf]
  refine ⟨(X.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint G)).hom, ?_⟩
  change _ = Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint G)).hom) ≫ _
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem surjective_of_generic {G X : Scheme.{0}} [IsIntegral G] [IsIntegral X] (f : G ⟶ X) [IsFinite f]
    (hf : f (genericPoint G) = genericPoint X) : Surjective f := by
  refine ⟨fun x => ?_⟩
  have hc : IsClosed (Set.range f.base) := f.isClosedMap.isClosed_range
  have hx : x ∈ closure {genericPoint X} := by
    have := genericPoint_spec X
    rw [this.def]; trivial
  have hsub : closure {genericPoint X} ⊆ Set.range f.base :=
    closure_minimal (by rintro _ rfl; exact ⟨_, hf⟩) hc
  exact hsub hx

end GlobalTheory.FlagGenFib
end
end

