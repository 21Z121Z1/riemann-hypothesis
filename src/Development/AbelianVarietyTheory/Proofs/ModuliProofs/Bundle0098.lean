import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0096
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPeriod

theorem adjoint_baseChange {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : B' ⟶ B} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (h : IsGrpPullback G' G f φ) (hb : LBIso L' (L.pull φ)) {w wd : G ⟶ G} {w' wd' : G' ⟶ G'}
    (hw : w'.left ≫ φ = φ ≫ w.left) (hwd : wd'.left ≫ φ = φ ≫ wd.left)
    (ha : LBIso (cubeLB G ![fst G G ≫ w, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ wd] L)) :
    LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ wd'] L') := by
  have pa : ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have pd : ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ wd') = pushPt h.1.w x ≫ wd := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hwd, Category.assoc])
  have hB : (L.pull φ).IsLB := pull_isLB hL φ
  have h₁ : LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] (L.pull φ))
      (cubeLB G' ![fst G' G', snd G' G' ≫ wd'] (L.pull φ)) := by
    let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
    refine LBIso.chartPull (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) ha
    · fin_cases i
      · exact (pa _).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pd _).trans (by simp [U])
  exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _)
    (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
    (LBIso.trans (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁
      (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _))

def tateIsoMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
    {Q Q' : Type} [Group Q] [Group Q'] {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop}
    {e' : ℕ → Q' → Q' → kˣ → Prop} (I : TateIso D k Q act e) (ψ : Q ≃* Q')
    (ha : ∀ c y, ψ (act c y) = act' c (ψ y)) (he : ∀ n y y' c, e n y y' c → e' n (ψ y) (ψ y') c) :
    TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n x := ψ (I.ev n x)
  add n x y := by rw [I.add, map_mul]
  lin n c x := by rw [I.lin, ha]
  ker n hn x := by rw [← I.ker n hn, map_eq_one_iff ψ ψ.injective]
  onto n hn x := by
    obtain ⟨x, rfl⟩ := ψ.surjective x
    rw [← map_pow, map_eq_one_iff ψ ψ.injective, I.onto n hn]
    simp only [ψ.injective.eq_iff]
  tower n m hn hm x := by rw [← map_pow, I.tower n m hn hm]
  isom n hn x y := he _ _ _ _ (I.isom n hn x y)

theorem exists_act {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {o : Type}
    [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {em : o →+* ℂ} {a : J → 𝓞 E}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {ρ : o} {t : TObj g k J b (spMap em)} (h : PELClass D a bas ρ em t) :
    ∃ act : OAct (𝓞 E) t.pol.A, (∀ j, act.act (a j) = t.act j) ∧ DetCond D act (𝟙 (Sp ℂ)) (em ρ) ∧
      (∀ c, LBIso (cubeLB t.pol.A ![fst t.pol.A t.pol.A ≫ act.act c, snd t.pol.A t.pol.A] t.pol.L)
        (cubeLB t.pol.A ![fst t.pol.A t.pol.A, snd t.pol.A t.pol.A ≫ act.act (H.bar c)] t.pol.L)) ∧
      ∃ I : TateIso D ℂ (Over.mk (𝟙 (Sp ℂ)) ⟶ t.pol.A) (fun c y => y ≫ act.act c)
          (fun n y y' c => Out.WeilIs t.pol.A t.pol.L n y y' (unitOn c)),
        (I.ζ k : ℂ) = em b.ζ ∧ ∀ i, (I.ev k (bas (Pi.single i 1))).left = (t.pt i).left := by
  obtain ⟨τ, φ, hφ, hL, hj, hd⟩ := h
  haveI := hφ
  haveI := t.ab.comm
  have hi : IsGrpPullback t.A τ.G (𝟙 _) φ.inv.left := GlobalTheory.FibreAct.isGrpPullback_of_iso φ.inv
  have e₁ : φ.inv.left ≫ φ.hom.left = 𝟙 _ := by rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]
  have hL' : LBIso t.L (τ.PP.L.pull φ.inv.left) :=
    LBIso.chartPull (chartPullSec t.L _ _ e₁) (chartPullPull τ.PP.L _ _ rfl) hL.symm
  obtain ⟨act, hact⟩ := GlobalTheory.FibreAct.exists_lift_act hi τ.act
  have hact' : ∀ c, act.act c ≫ φ.inv = φ.inv ≫ τ.act.act c := fun c => Over.OverMorphism.ext (hact c)
  have hact'' : ∀ c, τ.act.act c ≫ φ.hom = φ.hom ≫ act.act c := fun c => by
    rw [← Iso.inv_comp_eq, ← Category.assoc, ← hact', Category.assoc, φ.inv_hom_id, Category.comp_id]
  obtain ⟨hdet, I, hζ, hpt⟩ := hd ℂ (𝟙 _) em (Category.id_comp _)
  refine ⟨act, fun j => ?_, fun σ => ?_, fun c => ?_, ?_⟩
  · exact (cancel_epi φ.hom).1 ((hact'' _).symm.trans (hj j))
  · have L : ∀ n, LieMult act (𝟙 _) σ n ↔ LieMult τ.act (𝟙 _) σ n := fun n => by
      rw [GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hi hact ℂ _ σ n, Category.comp_id]
    exact ⟨fun hs => (L _).2 ((hdet σ).1 hs), fun hs => (L _).2 ((hdet σ).2 hs)⟩
  · exact adjoint_baseChange τ.PP.isLB t.isLB hi hL' (hact c) (hact _) (τ.adj c)
  · let ψ : (Over.mk (𝟙 (Sp ℂ)) ⟶ τ.G) ≃* (Over.mk (𝟙 (Sp ℂ)) ⟶ t.A) :=
      { toFun := fun y => y ≫ φ.hom
        invFun := fun y => y ≫ φ.inv
        left_inv := fun y => by simp
        right_inv := fun y => by simp
        map_mul' := fun y y' => MonObj.mul_comp _ _ _ }
    have W : ∀ (s : Sp ℂ ⟶ Sp ℂ), 𝟙 (Sp ℂ) ≫ 𝟙 (Sp ℂ) = s → ∀ (n : ℤ) (x y : Over.mk (𝟙 (Sp ℂ)) ⟶ t.A)
        (x₀ y₀ : Over.mk s ⟶ τ.G) (c : Γ(Sp ℂ, ⊤)ˣ), x₀.left = x.left ≫ φ.inv.left →
        y₀.left = y.left ≫ φ.inv.left → Out.WeilIs τ.G τ.PP.L n x₀ y₀ c → Out.WeilIs t.A t.L n x y c := by
      rintro _ rfl n x y x₀ y₀ c hx hy
      exact (GlobalTheory.weilIs_grpPullback_of_comm _ _ τ.G t.A _ _ _ _ τ.PP.isLB t.isLB hi hL' (Over.mk (𝟙 _)) n x y
        x₀ y₀ c hx hy).2
    have hψ : ∀ y : Over.mk (𝟙 (Sp ℂ)) ⟶ τ.G, y.left = (ψ y).left ≫ φ.inv.left := fun y => by
      show y.left = ((y ≫ φ.hom) ≫ φ.inv).left
      simp
    refine ⟨tateIsoMap I ψ (fun c y => ?_) (fun n y y' c => W _ (Category.id_comp _) n _ _ y y' _ (hψ y) (hψ y')),
      hζ, fun i => ?_⟩
    · show (y ≫ τ.act.act c) ≫ φ.hom = (y ≫ φ.hom) ≫ act.act c
      rw [Category.assoc, hact'', Category.assoc]
    · exact (congrArg (fun z => z.left) (hpt i)).trans (Category.id_comp _)

end GlobalTheory.PELPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubWeilPerfectOfGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_cubWeil_trivial_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [IsAlgClosed K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) → ∀ (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ (L : RigLB A) (c : CubicalStr A L) (n : ℕ), 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left → Flat ((𝟙 A) ^ n : A ⟶ A).left → Nat.card {x : specO O K ⟶ A // x ^ n = 1} = n ^ (2 * g) → (∀ x : specO O K ⟶ A, x ^ n = 1 → (∀ y : specO O K ⟶ A, y ^ n = 1 → GlobalTheory.UU.CubWeil c n x y 1) → x = 1) → ∀ (T : Over (Sp O)) (x : T ⟶ A), x ^ n = 1 → (∀ (T' : Over (Sp O)) (ρ : T' ⟶ T) (y : T' ⟶ A), y ^ n = 1 → GlobalTheory.UU.CubWeil c n (ρ ≫ x) y 1) → x = 1 := by
  first | exact @GlobalTheory.cubWeil_perfect_of_generic | exact GlobalTheory.cubWeil_perfect_of_generic | (intros; apply GlobalTheory.cubWeil_perfect_of_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAnalyticKodairaSpencerClassStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_kodairaSpencer_class : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D, IsDer x₀ D → ∃ Θ s, KSRel u p m D Θ s := by
  first | exact @GlobalTheory.KS.Exist.exists_ksRel | exact GlobalTheory.KS.Exist.exists_ksRel | (intros; apply GlobalTheory.KS.Exist.exists_ksRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerCommutesWithEndomorphismStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_commutes_with_endomorphism : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ (f : X ⟶ X) (f₀ : P₀.A ⟶ P₀.A) (F : (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)), f ≫ p = p → f₀.left ≫ m = m ≫ f → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm Θ F := by
  first | exact @GlobalTheory.KS.Endo.comm_of_endo | exact GlobalTheory.KS.Endo.comm_of_endo | (intros; apply GlobalTheory.KS.Endo.comm_of_endo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegersStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_psi_pull_localRingsOfIntegers : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (j : D.P.L.ι) (j' : D'.P.L.ι), ⊤ ≤ (D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U j → ⊤ ≤ (D'.c χ).left ⁻¹ᵁ D'.P.L.U j' → ‖algebraMap (FractionRing V') (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V'))) _ ((D'.psi χ).s fun _ => j').val)‖ = ‖algebraMap (FractionRing V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V))) _ ((D.psi (hD.xe χ)).s fun _ => j).val)‖ := by
  first | exact @GlobalTheory.ZH.PsiNormPull.norm_psi_pull | exact GlobalTheory.ZH.PsiNormPull.norm_psi_pull | (intros; apply GlobalTheory.ZH.PsiNormPull.norm_psi_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvrStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicIntermediateFieldIntRing_complete_dvr : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → IsDiscreteValuationRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ IsAdicComplete (IsLocalRing.maximalIdeal (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ ∀ x : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K), ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K))) := by
  first | exact @GlobalTheory.intRing_complete_dvr | exact GlobalTheory.intRing_complete_dvr | (intros; apply GlobalTheory.intRing_complete_dvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaValueTorsionFrame
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaCompare

private theorem pow_eq_one_of_three_pow_relations {G : Type*} [CommGroup G] (M : ℕ) (U0 Ax Ap A0 F R : G)
    (h1 : U0 ^ M * (Ax ^ M * Ap) = A0 ^ M * A0) (h2 : F ^ M * A0 = Ap * R ^ M) (h3 : A0 = R ^ M * R⁻¹) :
    (U0 * Ax * F * (R ^ M)⁻¹) ^ M = 1 := by
  rw [mul_pow, mul_pow, mul_pow, inv_pow, mul_inv_eq_one]
  apply mul_right_cancel (b := Ap * A0)
  calc U0 ^ M * Ax ^ M * F ^ M * (Ap * A0) = (U0 ^ M * (Ax ^ M * Ap)) * (F ^ M * A0) := by ac_rfl
    _ = (A0 ^ M * A0) * (Ap * R ^ M) := by rw [h1, h2]
    _ = (A0 ^ M * R ^ M) * (Ap * A0) := by ac_rfl
    _ = (R ^ M) ^ M * (Ap * A0) := by
      congr 1
      rw [h3, mul_pow, inv_pow, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]

open CommPairing in

theorem normalised_root_stalk {S : Scheme.{0}} (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {m : ℕ} (hm : Odd m)
    {rig : LB.Gen (P.L.pull (eSec P.A))} {th : LB.Sec (LPow P.A P.L 1 T)} {x p : T ⟶ P.A} (hx : x ^ m = p)
    {fr : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => p.left) (fun _ => 1))}
    (hfr : IsTorsFrame P rig m p fr) {t v : Γ(T.left, ⊤)} (ht : IsValueAt P.A P.L 1 th p fr t)
    (a : ℤ) (ha : a = (m : ℤ) ^ 2) {s₁ s₂ : LB.Sec (LPow P.A P.L a T)}
    (h₁ : GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsMulPull P rig m a th s₁) {U : ThetaGrp P.A P.L a T}
    (hU : SymLift P.A P.L a (m ^ 2) x U) (hs₂ : IsActOf P.A P.L a U s₁ s₂)
    (h₃ : GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsValueZero P rig a s₂ v) (y : T.left) :
    ∃ ξ : (T.left.presheaf.stalk y)ˣ, ξ ^ (m ^ 2) = 1 ∧ gs (𝟙 _) y ⊤ v = ξ.val * gs (𝟙 _) y ⊤ t := by
  subst ha
  unfold IsActOf at hs₂
  obtain ⟨α, hα, hαn, htw⟩ := h₁
  obtain ⟨τ₀, -, hτ₀, hval⟩ := h₃
  obtain ⟨J, hJ, -⟩ := exists_good (L := P.L) P.isLB y (Empty.elim : Empty → (T.left ⟶ P.A.left)) Empty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hxM : x ^ (m ^ 2) = 1 := by rw [sq, pow_mul, hx, hfr.1]
  have hR : ∀ k : ℕ, val rig T.hom y J ^ (k : ℤ) = val rig T.hom y J ^ k := fun k => zpow_natCast _ _
  have e1 := sval_valueAt hval hJ
  have e2 := sval_twist hs₂ (ptSecT P.A 1).left hJ
  have hpt : (ptSecT P.A (U.pt * 1)).left = (ptSecT P.A x).left := by rw [_root_.mul_one, hU.pt_eq]
  rw [pt_translT, hpt] at e2
  have e3 := sval_twist htw (ptSecT P.A x).left hJ
  rw [pt_mulT, hx] at e3
  have e4 := sval_valueAt ht hJ
  have e5 : val τ₀ (𝟙 _) y J = val rig T.hom y J ^ (m ^ 2) := by
    rw [val_corr hJ hτ₀, val_rigT rig _ hJ, ← Nat.cast_pow, hR]
  have F1 := frame_pow hG P hm hα hxM hU hJ
  rw [hx] at F1
  have F2 := torsFrame_pow hG P hα hfr hJ
  have F3 := val_corr hJ hαn (𝟙 _)
  rw [val_pull hJ, val_mul hJ, val_inv, val_rigT rig _ hJ, val_rigT rig _ hJ, Category.id_comp] at F3
  have F3' : val α (ptSecT P.A 1).left y J = val rig T.hom y J ^ (m ^ 2) * (val rig T.hom y J)⁻¹ := by
    rw [F3, zpow_one, ← hR, Nat.cast_pow]
  refine ⟨tval U (ptSecT P.A 1).left y J * val α (ptSecT P.A x).left y J * val fr (𝟙 _) y J *
    (val rig T.hom y J ^ (m ^ 2))⁻¹, pow_eq_one_of_three_pow_relations _ _ _ _ _ _ _ F1 F2 F3', ?_⟩
  calc gs (𝟙 _) y ⊤ v = gs (𝟙 _) y ⊤ v * (val τ₀ (𝟙 _) y J).val * (val τ₀ (𝟙 _) y J)⁻¹.val := by
        rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    _ = _ := by
        rw [← e1, e2, e3, e4, e5, show tval U (ptSecT P.A 1).left y J = val U.φ (ptSecT P.A 1).left y J from rfl]
        simp only [Units.val_mul]
        ring

end GlobalTheory.ThetaCompare

namespace GlobalTheory

end GlobalTheory
end
end

