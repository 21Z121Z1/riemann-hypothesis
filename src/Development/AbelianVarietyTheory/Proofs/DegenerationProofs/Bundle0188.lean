import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0187
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedLabelsAllLevelsOfFourLe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomAlgebraisationOfReductionTowerStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_algebraisation_of_reductionTower : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ Z : Over (Spec (CommRingCat.of R)), IsProjBy Z.hom → ∀ c : ∀ e, (Y e).left ⟶ Z.left, (∀ e, c e ≫ Z.hom = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ c (e + 1) = c e) → ∃ g : B ⟶ Z, ∀ e, b e ≫ g.left = c e := by
  first | exact @GlobalTheory.MorAlgTower.exists_hom_of_tower | exact GlobalTheory.MorAlgTower.exists_hom_of_tower | (intros; apply GlobalTheory.MorAlgTower.exists_hom_of_tower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PerpTorus
open GlobalTheory.ZH.TorusPerp GlobalTheory.TorusExt

theorem exists_form {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) {X : Type} [AddCommGroup X]
    (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) (hs : Function.Surjective yy)
    (a : S.Gam) (ha : a ∈ S.perp yy.ker) :
    ∃ m : X →+ ZMod (S.r * S.N), ∀ b α, yy b = QuotientAddGroup.mk α → m α = eStd S.g _ a b := by
  choose σ hσ using fun α : X => hs (QuotientAddGroup.mk α)
  have ind : ∀ b b' : S.Gam, yy b = yy b' → eStd S.g _ a b = eStd S.g _ a b' := by
    intro b b' e
    have h0 : eStd S.g _ a (b - b') = 0 := ha _ (by rw [AddMonoidHom.mem_ker, map_sub, e, sub_self])
    rw [← sub_add_cancel b b', eStd_add_right, h0, zero_add]
  refine ⟨AddMonoidHom.mk' (fun α => eStd S.g _ a (σ α)) fun α β => ?_, fun b α e => ind _ _ ((hσ α).trans e.symm)⟩
  rw [← eStd_add_right]
  exact ind _ _ (by rw [map_add, hσ, hσ, hσ, QuotientAddGroup.mk_add])

attribute [local instance] gtGroup in

theorem exists_torus_point : LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (g : u.Geom) (a : S.Gam) (ha : a ∈ S.perp l.yy.ker), ∃ (q : QkPt u.D.toPre (PadicAlgCl p) S.N) (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) S.N q (g.pt (S.r • a)) ∧ ∀ χ, (τ (Multiplicative.ofAdd χ) : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζN ^ (l.wt χ ⟨a, ha⟩).val)) := by
  intro hL hT o Ω _ _ _ hA S ρ p _ y₀ u l g a ha
  have hG := hL.1.globalFns
  have hN := S.N_ge
  have hr := S.r_pos
  have hn : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : IsDomain o := hA.inj.isDomain _
  have : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hadm : AdmBase u.V (maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hB := u.D.tau_bimult
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn.pos

  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (pow_pos hn.pos 2) (pow_two _)
  let ω : (PadicAlgCl p)ˣ := Units.map (y₀.comp (algebraMap o S.R)).toMonoidHom (hζ.isUnit hn.ne).unit
  have hωv : (ω : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N))) := rfl
  have hω : IsPrimitiveRoot ω (S.r * S.N) := by
    have : NeZero ((S.r * S.N : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.2 hn.ne⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (y₀.comp (algebraMap o S.R))]
    exact (hζ.isRoot_cyclotomic hn.pos).map

  let pt : Multiplicative S.Gam →* (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) :=
    MonoidHom.mk' (fun a => g.pt a.toAdd) fun _ _ => g.pt_add _ _
  have pt_nsmul : ∀ (n : ℕ) b, g.pt (n • b) = g.pt b ^ n := fun n b => map_pow pt (Multiplicative.ofAdd b) n
  have onto : ∀ b, ∃ q, f q = g.pt b := fun b => f₂ _ (by
    rw [← pt_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self, zero_smul]
    exact map_one pt)
  obtain ⟨m, hm⟩ := exists_form S l.yy l.yy_onto a ha
  let τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ :=
    (AddChar.zmodChar (S.r * S.N) hω.pow_eq_one).toMonoidHom.comp m.toMultiplicative
  have hτ : ∀ α, τ (Multiplicative.ofAdd α) = ω ^ (m α).val := fun _ => rfl
  have hτ1 : τ ^ (S.r * S.N) = 1 := MonoidHom.ext fun α => by
    show (ω ^ (m α.toAdd).val) ^ (S.r * S.N) = 1
    rw [pow_right_comm, hω.pow_eq_one, one_pow]
  obtain ⟨q, hq, hqτ⟩ := exists_qkPt_tor (F := PadicAlgCl p) hB τ hτ1
  obtain ⟨q₁, hq₁, hq₁τ⟩ := exists_qkPt_tor (F := PadicAlgCl p) (k := S.N) hB (τ ^ S.r) (by rw [← pow_mul, hτ1])
  have hq1 : f q ^ (S.r * S.N) = 1 := by
    obtain ⟨w, hw⟩ := u.U.ext
    exact ((f₁ _ _).2 rfl w hw).1
  obtain ⟨a', ha', -⟩ := g.pt_bij (f q) hq1
  have haa : a' = a := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eStd _ _ _ fun b => ?_
    obtain ⟨q', hq'⟩ := onto b
    have w₁ := (f₅ q q' _).1 (weilQkIs_tor hG q q' hq hqτ)
    rw [← ha', hq'] at w₁
    have w₂ := g.weil a' b (ω ^ (eStd S.g _ a' b).val) (by
      rw [Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, ← pow_mul])
    have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB w₂ w₁)
    rw [hτ] at e₁
    have e₂ := ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₁)
    rw [hm b _ (l.yy_eq b q' _ ((f₁ _ _).2 hq'.symm) (g.pt_over b))] at e₂
    have e₃ := eStd_add_left S.g _ (a' - a) a b
    rw [sub_add_cancel, e₂] at e₃
    exact left_eq_add.1 (e₃.trans (add_comm _ _))
  subst haa
  refine ⟨q₁, τ ^ S.r, hq₁, hq₁τ, ?_, fun χ => ?_⟩
  · rw [pt_nsmul]
    refine (GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N S.r (S.r * S.N) (by omega) hr
      (mul_comm _ _) q₁ q _).2 (hq₁.trans hq.symm) ((isNsmul_iff_eq _ _ _).2 ?_) ((f₁ _ _).2 ha')
    rw [(isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 hq₁τ), (isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 hqτ),
      ofMul_pow, map_nsmul]
  · obtain ⟨b, hb⟩ := l.yy_onto (QuotientAddGroup.mk χ)
    have z : S.ζN ^ S.N = 1 := by
      rw [ThetaSys.ζN, ← pow_mul, ← S.prim.pow_eq_one]
      congr 1
      ring
    have z' : S.ζN = (S.ζ ^ (S.r * S.N)) ^ S.r := by
      rw [ThetaSys.ζN, ← pow_mul]
      congr 1
      ring
    rw [l.wt_eq b χ hb, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, ← pow_eq_pow_mod _ z,
      MonoidHom.pow_apply, hτ, hm b χ hb, z', pow_right_comm, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hωv,
      ← map_pow, ← map_pow, ← map_pow, ← map_pow]

end GlobalTheory.ZH.PerpTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitValue
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.SecValue
open GlobalTheory.UT.CoefBasic

theorem exists_pow {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ} (n : ℕ)
    (h : ε' = fun i => (n : ℤ) * ε i) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε'), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), val t' r z J = val t r z J ^ n := by
  subst h
  exact ⟨GeneratorPullback.powGen L φ ε t n, powGen_isGen L φ ε t ht n, fun _ _ _ _ => map_pow _ _ _⟩

theorem line_exp (k : ℕ) : DegPre.lineε k = fun i => (k : ℤ) * DegPre.lineε 1 i := by
  funext i
  fin_cases i <;> simp [DegPre.lineε]

theorem le_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (hq : ∀ i, (q : WithTop ℚ) ≤ v (x i)) : (q : WithTop ℚ) ≤ v s := by
  obtain ⟨S, hS⟩ := h q
  have := v.map_le_add (hS S le_rfl) (v.map_le_sum (s := S) fun i _ => hq i)
  rwa [sub_add_cancel] at this

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {hϖ : Irreducible ϖ}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {hv : ValOver ϖ F v}
  {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ X)}

theorem genV_pow {ε ε' : K → ℤ} (n : ℕ) (h : ε' = fun i => (n : ℤ) * ε i) {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ ε')} (ht : GenV hϖ hv t 0)
    (e : ∀ z J, Good L z J → val t' (𝟙 _) z J = val t (𝟙 _) z J ^ n) : GenV hϖ hv t' 0 := by
  obtain ⟨φ₀, hφ, t₀, ht₀, x, hx, hval⟩ := ht
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_pow n h t₀ ht₀
  refine ⟨φ₀, hφ, t₁, ht₁, x ^ n, ?_, fun z J hJ => ?_⟩
  · rw [v.map_pow, hx]; simp
  · rw [e z J hJ, hv₁, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hval z J hJ, mul_pow, cst_eq, cst_eq, map_pow]

end

section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

abbrev kon (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    F →+* Γ((TFK (R := R) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem kon_surj : Function.Surjective (kon R F) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2

theorem isComb_iff {J : Type} [Fintype J] (t : J → SecA A F k) (b : J → F) (σ : SecA A F k) :
    IsComb t b σ ↔ SecM.ofSec A.A σ = ∑ l, kon R F (b l) • SecM.ofSec A.A (t l) := by
  rw [Subtype.ext_iff, funext_iff, Submodule.coe_sum]
  refine forall_congr' fun j => ?_
  rw [Finset.sum_apply]
  rfl

def ValM (σ : SecM A.A A.L k (TFK (R := R) F)) (x : TFK (R := R) F ⟶ A.A) (e : FrAt x) (c : F) : Prop :=
  ValAt (SecM.toSec A.A σ) x e c

theorem ValM.add {σ σ' : SecM A.A A.L k (TFK (R := R) F)} {x e} {c c' : F} (h : ValM σ x e c) (h' : ValM σ' x e c') :
    ValM (σ + σ') x e (c + c') := fun z J hJ => by
  refine (ThetaAct.sv_add σ σ' _ z hJ).trans ((congrArg₂ (· + ·) (h z J hJ) (h' z J hJ)).trans ?_)
  simp only [id, cst_eq, map_add]
  exact (add_mul (R := (TFK (R := R) F).left.presheaf.stalk z) _ _ _).symm

theorem ValM.smul {σ : SecM A.A A.L k (TFK (R := R) F)} {x e} {c : F} (h : ValM σ x e c) (b : F) :
    ValM (kon R F b • σ) x e (b * c) := fun z J hJ => by
  refine (ThetaAct.sv_smul _ σ _ z hJ).trans ?_
  rw [ThetaPtMove.ptSecT_fst]
  refine (congrArg (@id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z b) * ·) (h z J hJ)).trans ?_
  simp only [id, cst_eq, map_mul]
  exact (_root_.mul_assoc (G := (TFK (R := R) F).left.presheaf.stalk z) _ _ _).symm

theorem ValM.unique {σ : SecM A.A A.L k (TFK (R := R) F)} {x e} {c c' : F} (h : ValM σ x e c) (h' : ValM σ x e c') :
    c = c' := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  have := (Units.mul_left_inj _).1 ((h z J hJ).symm.trans (h' z J hJ))
  simp only [id, cst_eq] at this
  exact cstH_inj z this

theorem ValM.exists (hL : Laws) (σ : SecM A.A A.L k (TFK (R := R) F)) {x} {e : FrAt x} (he : e.IsGen) :
    ∃ c, ValM σ x e c := by
  obtain ⟨w, hw, -⟩ := hL.evVal _ A k x e he (SecM.toSec A.A σ)
  obtain ⟨c, rfl⟩ := kon_surj w
  refine ⟨c, fun z J hJ => ?_⟩
  have := ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ
  rw [Category.id_comp] at this
  exact this

theorem ValM.sum (hL : Laws) {x} {e : FrAt x} (he : e.IsGen) {J : Type} (s : Finset J)
    {σ : J → SecM A.A A.L k (TFK (R := R) F)} {c : J → F} (h : ∀ l, ValM (σ l) x e (c l)) :
    ValM (∑ l ∈ s, σ l) x e (∑ l ∈ s, c l) := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨c, hc⟩ := ValM.exists hL (0 : SecM A.A A.L k (TFK (R := R) F)) he
    have := hc.smul 0
    rw [smul_zero, zero_mul] at this
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add ih

end

theorem val_sum_eq_zero {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) (i₀ : Ix) (h₀ : v (x i₀) = 0) {q : ℚ} (hq : 0 < q)
    (hx : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (x i)) : v s = 0 := by
  obtain ⟨S, hS⟩ := h q
  have a := hS (insert i₀ S) (Finset.subset_insert _ _)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self i₀ S)] at a
  have b := v.map_le_add a (v.map_le_sum (s := (insert i₀ S).erase i₀) fun i hi => hx i (Finset.ne_of_mem_erase hi))
  have e : s = x i₀ + (s - (x i₀ + ∑ i ∈ (insert i₀ S).erase i₀, x i) + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by ring
  rw [e, v.map_add_eq_of_lt_left, h₀]
  rw [h₀]
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 hq) b

theorem exists_unit_value : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (n k : ℕ), 1 ≤ n → 4 ≤ k → ∀ (p : QkPt D.toPre F n) x, p.y = 0 → QkToAkU U.toUnifPre F n p x → ∀ e, IsTorsFrame A ρ n x e → ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ (∀ β, (∀ z : D.toPre.X, β ≠ k • z) → ∀ j, (s.s β).f j = 0) ∧ ∀ (t : SecA A F k) (c : F), U.ExpandsF F k w₀ t s → ValAt t x e c → v c = 0 := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN n k hn hk p x hy hx e he
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.UT.TorsionValue.value_at_torsion hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv
    A G hG U w₀ ρ hN n hn p x hx e he
  rw [hy, QForm.Q_zero hϖ D hQ, Int.cast_zero, zero_div] at hv₁
  obtain ⟨-, -, -, -, hqk, -, hterm⟩ := GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv p.g
  obtain ⟨w, hw, hwv⟩ := exists_pow k (line_exp k) w₁ hw₁
  have hw0 : GenV hϖ hv w 0 := genV_pow k (line_exp k) hv₁ fun z J _ => hwv _ _ z J
  have b0 : ∀ χ, QForm.bOf D.toPre Q p.y χ = 0 := fun χ => by
    rw [hy, QForm.bOf, zero_add, QForm.Q_zero hϖ D hQ]; ring
  have hg := hqk n hn p
  obtain ⟨s, hν, hsupp, hc₀⟩ := GlobalTheory.UT.CoefUnit.exists_fam_coef_val hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv k hk
    p.g w _ 0 hw hg hw0 0
  refine ⟨s, hν, fun β hβ => hsupp β fun z => by simpa using hβ z, fun t c ht hc => ?_⟩
  have hS : SumV v (coef s p.g w) c := hsum k hk1 w ⟨hw, fun z J _ => hwv _ _ z J⟩ t s c ht hc
  have hk0 : (0 : ℚ) < k := by exact_mod_cast hk1
  refine val_sum_eq_zero hS 0 ?_ (q := 1 / k) (by positivity) fun χ hχ => ?_
  · rw [hc₀, b0, QForm.Q_zero hϖ D hQ]; simp
  · refine le_trans (WithTop.coe_le_coe.2 ?_) ((hterm k hk1 w s hw).2 _ 0 0 hg hw0 hν χ)
    rw [b0]
    have : (1 : ℚ) ≤ Q χ := by exact_mod_cast QForm.Q_pos hϖ D hQ hχ
    simpa using div_le_div_of_nonneg_right this hk0.le

theorem act_fix : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) τ x, p.y = 0 → IsTor τ p.g → QkToAkU U.toUnifPre F N p x → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (t t' : SecA A F N) s, U.ExpandsF F N w₀ t s → (∀ β, τ (Multiplicative.ofAdd β) = 1 ∨ ∀ j, (s.s β).f j = 0) → IsActOf A.A A.L N θ t t' → t' = t := by
  intro hL R _ _ _ I hA D A G _ _ hG U F _ _ _ N hN p τ x hy hτ hx θ hθ w₀ hw₀ t t' s hs hsupp hact
  obtain ⟨hb₁, hb₂⟩ := (GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hA D A G hG U).1 F N hN.pos w₀ hw₀
  obtain ⟨s', hs', -⟩ := hb₁ t'
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL R I hA D F N hN p).1
  have hφ := GlobalTheory.UT.symLift_acts_as_phi hL R I hA D A G hG U F N hN p x hx θ hθ w₀ hw₀ w hw t t' s s' hs hs' hact
  have e := ((GlobalTheory.UT.TorusWeight.torus_weight hL R I hA D A G hG U F N hN p τ hy hτ w hw).2 s s').1 hφ
  obtain rfl : s' = s := fam_ext fun α j => by
    rw [e α j]
    rcases hsupp α with h | h
    · rw [h, Units.val_one, DegPre.constBF, map_one, map_one, map_one, _root_.one_mul]
    · rw [h j, mul_zero]
  exact (hb₂ s').unique hs' hs

end GlobalTheory.ZH.SecValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FromGtOfMemUnitGrp
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitGrp
open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem fromGt_of_mem_unitGrp : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ k : ℕ, Odd k → IsUnit (k : V) → ∀ x ∈ unitGrp v ρ th k, FromGt U.toUnifPre k x := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP k hk hu x hx
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  obtain ⟨f, f₁, -, f₃, f₄, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hA D A G hG U F k hk.pos
  obtain ⟨f', f₁', f₂', -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hA D A G hG U F (k ^ 2) (pow_pos hk.pos 2)
  have ua := (GlobalTheory.T.theta_constant_valuations_units_every_coset hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ hE hP k hk hu).1
  have add : ∀ p p', f (qkAdd hB p p') = f p * f p' := fun p p' => f₄ _ _ _ (qkAdd_qkAdd hB p p')
  have f0 : f (qkZero hB F k) = 1 := by
    have e := add (qkZero hB F k) (qkZero hB F k)
    rw [show qkAdd hB (qkZero hB F k) (qkZero hB F k) = qkZero hB F k from qk_ext (add_zero _) (add_zero _)] at e
    exact mul_eq_left.1 e.symm
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, t, c, hx, hT, hc0, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := f₂' x hx
    have hq := (f₁' q _).2 rfl
    obtain ⟨z, hz⟩ := (ua q _ t c hq hT).2 hc0
    let p : QkPt D.toPre F k := qkMk hB q.y (k • q.g) (by rw [← mul_smul, ← pow_two, qk_nsmul hB])
    have hp := (GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D A G hG U F k k (k ^ 2) hk.pos hk.pos (pow_two k) p q (f' q)).2 rfl
      ((isNsmul_iff_eq _ _ _).2 rfl) hq
    refine ⟨qkShift hB p (-z), ?_, (f₁ _ _).2 (((f₁ _ _).1 hp).trans ((f₃ _ _).2 (equiv_qkShift hB p (-z))))⟩
    show q.y + k • (-z) = 0
    rw [hz, smul_neg, add_neg_cancel]
  | one => exact ⟨qkZero hB F k, rfl, (f₁ _ _).2 f0.symm⟩
  | mul a b _ _ ha hb =>
    obtain ⟨p, py, hp⟩ := ha
    obtain ⟨p', py', hp'⟩ := hb
    refine ⟨qkAdd hB p p', ?_, (f₁ _ _).2 ?_⟩
    · show p.y + p'.y = 0
      rw [py, py', add_zero]
    · rw [add, (f₁ _ _).1 hp, (f₁ _ _).1 hp']
  | inv a _ ha =>
    obtain ⟨p, py, hp⟩ := ha
    refine ⟨qkNeg hB p, ?_, (f₁ _ _).2 ?_⟩
    · show -p.y = 0
      rw [py, neg_zero]
    · have e := add (qkNeg hB p) p
      rw [show qkAdd hB (qkNeg hB p) p = qkZero hB F k from qk_ext (neg_add_cancel _) (neg_add_cancel _), f0] at e
      rw [(f₁ _ _).1 hp]
      exact (eq_inv_of_mul_eq_one_left e.symm).symm

end GlobalTheory.OneBasis.UnitGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfThetaUnitInEveryCosetStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_theta_unit_in_every_coset : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (n j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 2 ≤ j → ∀ v, o.Theta (n ^ j) v → (∀ x, ‖v x‖ ≤ 1) → (∀ x, ∃ h, ‖v (x + n ^ (j - 1) • h)‖ = 1) → IsProper M.t.G.hom := by
  first | exact @GlobalTheory.CosetGood.isProper_of_unit_in_cosets | exact GlobalTheory.CosetGood.isProper_of_unit_in_cosets | (intros; apply GlobalTheory.CosetGood.isProper_of_unit_in_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisedThetaConstantsPrimitiveIntegralOneUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

theorem GlobalTheory.Ex.OneGen.thG_val_of_prim : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → (∀ x (c : F), ThG A.A A.L ρ m th x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG A.A A.L ρ m th x (fnOf c) ∧ v c = 0 := by
  rintro ⟨hLL, h₁, h₂, h₃, h₄⟩ V _ _ _ _ hV ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hw th ϑ hex hprim m hmo hmu hm
  have hAdm : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨f, hf, hfs, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hLL V _ hAdm D A G hG U F (m ^ 2) (pow_pos hmo.pos 2)
  obtain ⟨ua, ub⟩ := GlobalTheory.T.theta_constant_valuations_units_every_coset hLL h₁ h₂ h₃ h₄ V hV ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hw th ϑ hex hprim m hmo hmu
  refine ⟨fun x c H => ?_, ?_⟩
  · obtain ⟨hx, t, ht⟩ := (thG_iff A ρ m th x c).1 H
    obtain ⟨p, hp⟩ := hfs x hx
    refine (ua p x t c ((hf p x).2 hp.symm) ht).1 0 fun χ => div_nonneg ?_ (Nat.cast_nonneg _)
    by_cases h : m • χ + p.y = 0
    · rw [h, QForm.Q_zero hϖ D hQ]; simp
    · exact_mod_cast zero_le_one.trans (QForm.Q_pos hϖ D hQ h)
  · obtain ⟨p', x', t, c, -, hx', -, hc, hz⟩ := ub m (by omega) dvd_rfl (TorusExt.qkZero D.tau_bimult F _) _ rfl
      ((hf _ _).2 rfl)
    exact ⟨x', c, (thG_iff A ρ m th x' c).2 ⟨(hx' w₀ hw.1).1, t, hc⟩, hz⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem psiUnitOn_abLocus_pel : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso → IsOpen (abLocus t.G) → ∀ y, PsiUnitOn P.D.toPre y (abLocus t.G) :=
  fun h1 h2 h3 h4 h5 _ _ _ _ _ R _ _ _ I hA t P _ ho y =>
    GlobalTheory.T.psiUnitOn_abelian_locus_uniformisation h1 h2 h3 h4 h5 R I hA P.D P.A t.G t.semi P.U ho y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianReductionOfIsogenyStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialSemiAbelianReduction_of_isogeny : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g m : ℕ), IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ (i : A ⟶ B) (r : B ⟶ A), IsMonHom i → IsMonHom r → 1 ≤ m → r ≫ i = 𝟙 _ ^ m → PotModel V K B (fun _ _ _ G _ => IsSemiAbelian G) → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) := by
  first | exact @GlobalTheory.SS.potModel_semiAbelian_of_isogeny | exact GlobalTheory.SS.potModel_semiAbelian_of_isogeny | (intros; apply GlobalTheory.SS.potModel_semiAbelian_of_isogeny <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedLabelsAllLevelsOfFourLeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedLabels_all_levels_of_four_le : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → (∀ k, 4 ≤ k → Labels A u r M ν' J k) → ∀ k, 0 < k → Labels A u r M ν' J k := by
  first | exact @GlobalTheory.Ex.LabelsAllLevels.labels_of_four_le | exact GlobalTheory.Ex.LabelsAllLevels.labels_of_four_le | (intros; apply GlobalTheory.Ex.LabelsAllLevels.labels_of_four_le <;> assumption)
end

