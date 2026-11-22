import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3371
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3441

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycle
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

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.HeatDefect

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ h) z U a = (r.stalkMap z).hom (gs h (r z) U a) := by
  rw [← gs_pull r h z U hU, gs_eq r z (h ⁻¹ᵁ U) hU, gs_eq h (r z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply r (h ⁻¹ᵁ U) z hU _).symm

theorem sval_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp_stalk r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem val_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    (val t (r ≫ h) z J).val = (r.stalkMap z).hom (val t h (r z) (fun ψ => J (r ≫ ψ))).val := by
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc]),
    val_of t h (r z) (fun ψ => J (r ≫ ψ)) (fun k => J (r ≫ h ≫ φ k)) (fun k => rfl)]
  have hm : (r ≫ h) z ∈ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  exact (gs_unit _ z _ hm _).symm.trans ((gs_comp_stalk r h z _ hm _).trans (congrArg _ (gs_unit h (r z) _ hm _)))

theorem good_comp {X Z : Scheme.{0}} {L : LB X} (r : Z ⟶ Z) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => by
  have := hJ (r ≫ ψ)
  rwa [Scheme.Hom.comp_apply] at this

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R}

theorem gs_scal (m : DegPre.BF Q (FractionRing R) ⟶ DegPre.BF Q (FractionRing R)) (z : (DegPre.BF Q (FractionRing R)).left)
    (c : R) : (m.left.stalkMap z).hom (gs (𝟙 _) (m.left z) ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c)) =
      gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c) := by
  rw [← gs_comp_stalk m.left (𝟙 _) z ⊤ trivial, Category.comp_id]
  unfold ReciprocityTheory.ChartRestriction.G.Out.scal
  have e₁ := gs_pull m.left (DegPre.BF Q (FractionRing R)).hom z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
  have e₂ := gs_pull (𝟙 _) (DegPre.BF Q (FractionRing R)).hom z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
  rw [Over.w m] at e₁
  rw [Category.id_comp] at e₂
  exact e₁.trans e₂.symm

end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect
variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R}

theorem shiftEq_at {k : ℕ} {mu α : Q.X} {σ : Q.SecB k α} {σ₁ σ₂ : Q.SecB k (α + k • mu)} {c : R}
    (H : ShiftEq Q k mu α σ σ₁ c σ₂)
    (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left)
      (DegPre.famMult Q (FractionRing R) k mu α))
    (m : DegPre.BF Q (FractionRing R) ⟶ DegPre.BF Q (FractionRing R)) (z : (DegPre.BF Q (FractionRing R)).left)
    (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι) (hJ : Good Q.P.L z J) :
    sval σ₁ (m ≫ DegPre.prB Q (FractionRing R)).left z J =
      (val u m.left z J).val *
          sval σ (m ≫ DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)).left z J +
        gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom c) *
          sval σ₂ (m ≫ DegPre.prB Q (FractionRing R)).left z J := by
  have e := congrArg (m.left.stalkMap z).hom (H u hu hc (m.left z) _ (good_comp m.left z hJ))
  rw [Over.comp_left, Over.comp_left, Over.comp_left, sval_comp_stalk _ _ _ _ hJ, sval_comp_stalk _ _ _ _ hJ,
    sval_comp_stalk _ _ _ _ hJ, e, map_add, map_mul, map_mul, gs_scal]
  congr 2
  have := val_comp_stalk u (𝟙 _) m.left z hJ
  rw [Category.comp_id] at this
  exact this.symm

end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect

theorem scal_injective (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) :
    Function.Injective (fun r : R => gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom r)) := by
  let F := FractionRing R
  let χ : F →+* (DegPre.BF Q F).left.presheaf.stalk z :=
    ((DegPre.BF Q F).left.presheaf.germ ⊤ z trivial).hom.comp
      ((fst (TF (R := R) F) Q.P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)
  have hT : (DegPre.BF Q F).hom = (fst (TF (R := R) F) Q.P.A).left ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [← Over.w (fst (TF (R := R) F) Q.P.A)]
    show _ ≫ (jFK (R := R) F ≫ jK R) = _
    rw [jFK, jK, ← Spec.map_comp]
    rfl
  have key : ∀ r : R, gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q F).hom r) = χ (algebraMap R F r) := by
    intro r
    unfold ReciprocityTheory.ChartRestriction.G.Out.scal
    rw [hT, gs_eq _ z ⊤ trivial]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R F))
    have n' := congrArg (fun f => f.hom r) n
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n'
    simp only [χ, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, n']
    rfl
  intro a b hab
  have : χ (algebraMap R F a) = χ (algebraMap R F b) := (key a).symm.trans (hab.trans (key b))
  exact IsFractionRing.injective R F (χ.injective this)
end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect

theorem sval_cast {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {k : ℕ} {x y : Q.X} (e : x = y)
    (he : Q.SecB k x = Q.SecB k y) (σ : Q.SecB k x) {Z : Scheme.{0}} (r : Z ⟶ Q.P.A.left) (z : Z)
    (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) : sval (cast he σ) r z J = sval σ r z J := by
  subst e; rfl

theorem tActs_cast {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} {Y : Ray oa} {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R}
    {h : Heat Y.H Y.q.left Q.P.L dd D} {k : ℕ} {x y : Q.X} (e : x = y) (he : Q.SecB k x = Q.SecB k y)
    {σ σ' : Q.SecB k x} (H : TActs Y h k x σ σ') : TActs Y h k y (cast he σ) (cast he σ') := by
  subst e; exact H

theorem scal_add {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) (a b : R) :
    gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom (a + b)) =
      gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom a) +
        gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom b) := by
  unfold ReciprocityTheory.ChartRestriction.G.Out.scal
  rw [map_add, map_add]
  exact gs_add (𝟙 _) z ⊤ trivial _ _

theorem scal_zero {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) :
    gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom 0) = 0 := by
  have := scal_add Q z 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem defect_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (c : ℕ → Dd.toPre.X → Dd.toPre.X → R), IsBasic Y h → HasDefect Y h c → ∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α, c k (mu + mu') α = c k mu α + c k mu' (α + k • mu) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv D h c hB hD k hk mu mu' α
  obtain ⟨σ, σ₁, σ₂, he, h1, h2, h3, z, J, hJ, hs⟩ := GlobalTheory.T.exists_integral_sections_thetaShift_triple R Dd k hk mu mu' α
  have e : α + k • mu + k • mu' = α + k • (mu + mu') := by rw [smul_add, add_assoc]
  obtain ⟨σ', a1⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h hB k α σ
  obtain ⟨σ₁', a2⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h hB k _ σ₁
  obtain ⟨σ₂', a3⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h hB k _ σ₂
  have d1 := hD k mu α σ σ' σ₁ σ₁' hk h1 a1 a2
  have d2 := hD k mu' (α + k • mu) σ₁ σ₁' σ₂ σ₂' hk h2 a2 a3
  have d3 := hD k (mu + mu') α σ σ' _ _ hk h3 a1 (tActs_cast e he a3)
  obtain ⟨⟨u1, hu1, hc1⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu α
  obtain ⟨⟨u2, hu2, hc2⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu' (α + k • mu)
  obtain ⟨⟨u3, hu3, hc3⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k (mu + mu') α
  have E1 := shiftEq_at d1 u1 hu1 hc1 (DegPre.trF Dd.toPre (FractionRing R) mu') z J hJ
  have E10 := shiftEq_at h1 u1 hu1 hc1 (DegPre.trF Dd.toPre (FractionRing R) mu') z J hJ
  have E2 := shiftEq_at d2 u2 hu2 hc2 (𝟙 _) z J hJ
  have E20 := shiftEq_at h2 u2 hu2 hc2 (𝟙 _) z J hJ
  have E3 := shiftEq_at d3 u3 hu3 hc3 (𝟙 _) z J hJ
  have E30 := shiftEq_at h3 u3 hu3 hc3 (𝟙 _) z J hJ
  simp only [Category.id_comp, scal_zero, zero_mul, add_zero] at E1 E10 E2 E20 E3 E30
  rw [sval_cast e he, sval_cast e he] at E3
  rw [sval_cast e he] at E30
  rw [← Category.assoc, UUA.trF_add, add_comm mu' mu] at E1 E10
  set s := sval σ (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set s' := sval σ' (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set v1 := (val u1 (DegPre.trF Dd.toPre (FractionRing R) mu').left z J).val
  set v2 := (val u2 (Over.Hom.left (𝟙 (DegPre.BF Dd.toPre (FractionRing R)))) z J).val
  set v3 := (val u3 (Over.Hom.left (𝟙 (DegPre.BF Dd.toPre (FractionRing R)))) z J).val
  set p1 := sval σ₁ (DegPre.trF Dd.toPre (FractionRing R) mu' ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set q := sval σ₂ (DegPre.prB Dd.toPre (FractionRing R)).left z J
  set C1 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k mu α))
  set C2 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k mu' (α + k • mu)))
  set C3 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k (mu + mu') α))
  have k1 : (v2 * v1 - v3) * s = 0 := by linear_combination (-v2) * E10 - E20 + E30
  have hv' : v2 * v1 - v3 = 0 := hs.mul_left_eq_zero.mp k1
  have k2 : (C3 - (C1 + C2)) * q = 0 := by linear_combination E2 - E3 + v2 * E1 + s' * hv' - C1 * E20
  have hq : IsUnit q := by
    rw [E30]; exact (Units.isUnit _).mul hs
  have hC : C3 = C1 + C2 := sub_eq_zero.mp (hq.mul_left_eq_zero.mp k2)
  rw [← scal_add] at hC
  exact scal_injective R Dd.toPre z hC

end GlobalTheory.HeatDefect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameGeneratorValuePullback
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

theorem gm_eq_of_appLE {T Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) {U : T.Opens} {W : Z.Opens} (hW : W ≤ r ⁻¹ᵁ U)
    (hz : z ∈ W) (u : Γ(T, U)ˣ) (v : Γ(Z, W)ˣ) (e : v.val = (r.appLE U W hW).hom u.val) :
    gm r z U u = gm (𝟙 Z) z W v := by
  refine Units.ext ?_
  rw [gm_val r z U (hW hz), gm_val (𝟙 Z) z W hz, e]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hW) z hz _).symm

theorem val_gen_pull : ∀ {S' T Z : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) (r : Z ⟶ T) {B : Over Z} [GrpObj B] {ρ : B.left ⟶ H.left}
    (q : IsGrpPullback B H r ρ) (x' : Z ⟶ S') (ψ' : B.left ⟶ G.left) (h' : IsGrpPullback B G x' ψ'),
    r ≫ x = x' → ρ ≫ ψ = ψ' → ∀ {b : Fin g → Γ(omega B, ⊤)} (hb : IsFrame b),
    (∀ i, b i = (omegaBase q).app ⊤ (pullbackSections r _ le_top (a i))) → ∀ (z : Z)
    (J : (Z ⟶ S') → (hodge G g).ι), Good (hodge G g) z J →
    val (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J =
      val (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J := by
  intro S' T Z G _ H _ x ψ _ g h a ha r B _ ρ q x' ψ' h' e e' b hb hab z J hJ
  have : QuasiSeparated H.hom := MorphismProperty.of_isPullback h.1 ‹_›
  rw [val_of (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J (fun _ => J x')
      (fun _ => by rw [e]),
    val_of (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J (fun _ => J x')
      (fun _ => by rw [Category.id_comp])]
  have hW : LB.wchart (hodge G g) (fun _ : PUnit => x') (fun _ => J x') ≤
      r ⁻¹ᵁ LB.wchart (hodge G g) (fun _ : PUnit => x) (fun _ => J x') := fun y hy =>
    Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy k
      rw [← e] at this ⊢
      exact this
  have hz : z ∈ LB.wchart (hodge G g) (fun _ : PUnit => x') (fun _ => J x') := Set.mem_iInter.2 fun _ => hJ x'
  have k {U : T.Opens} {V W : Z.Opens} (hV : V ≤ r ⁻¹ᵁ U) (h₁ : W ≤ V) (s : Γ(omega H, U)) :
      GlobalTheory.Twist.resM _ h₁ ((omegaBase q).app V (pullbackSections r _ hV s)) =
        (omegaBase q).app W (pullbackSections r _ (h₁.trans hV) s) := by
    rw [← GlobalTheory.QCoh.res_pullbackSections r _ hV h₁ s]
    exact congr($((omegaBase q).mapPresheaf.naturality (homOfLE h₁).op) (pullbackSections r _ hV s)).symm
  refine gm_eq_of_appLE r z hW hz _ _ ?_
  have hc := isFrame_chart h (fun _ => J x')
  refine Eq.trans ?_ (hc.val_detUnit_pullback ha r le_rfl le_top hW)
  refine congrArg Units.val ?_
  refine Eq.trans ?_ (IsFrame.detUnit_map_iso _ _ (omegaBase q) _ _)
  refine GlobalTheory.Vert.DivPull.detUnit_congr _ _ _ _ _ _ _ _ (fun i => ?_) (fun i => ?_)
  · refine Eq.trans (GlobalTheory.Twist.resM_self _ _) (Eq.trans ?_ (k _ _ _).symm)
    exact (GlobalTheory.BadPt.Fibre.omegaBase_comp h q h' e e' _ _ _ _).symm
  · rw [hab]
    exact (k _ _ _).trans (k _ _ _).symm

end GlobalTheory.HodgeFrameGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEndomorphismImageCommutesBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.ImgPB

@[reassoc]
theorem tensorHom_fst_left {B : Scheme.{0}} {X Y Z W : Over B} (f : X ⟶ Y) (h : Z ⟶ W) :
    (f ⊗ₘ h).left ≫ (fst Y W).left = (fst X Z).left ≫ f.left := by
  rw [← Over.comp_left, tensorHom_fst, Over.comp_left]

@[reassoc]
theorem tensorHom_snd_left {B : Scheme.{0}} {X Y Z W : Over B} (f : X ⟶ Y) (h : Z ⟶ W) :
    (f ⊗ₘ h).left ≫ (snd Y W).left = (snd X Z).left ≫ h.left := by
  rw [← Over.comp_left, tensorHom_snd, Over.comp_left]

theorem image_idem_pullback : ∀ (S' T : Scheme.{0}) (g : T ⟶ S') (A G : Over S') [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G) (ε : A ⟶ A) (A' G' : Over T) [GrpObj A'] [IsCommMonObj A'] [GrpObj G'] [IsCommMonObj G'] (inc' : G' ⟶ A') (pr' : A' ⟶ G') (ε' : A' ⟶ A') (ψ : A'.left ⟶ A.left) (ψ₂ : (G2 A').left ⟶ (G2 A).left), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = ε → IsMonHom inc' → IsMonHom pr' → inc' ≫ pr' = 𝟙 G' → pr' ≫ inc' = ε' → IsGrpPullback A' A g ψ → IsSquare ψ ψ₂ → ε'.left ≫ ψ = ψ ≫ ε.left → ∃ (φ : G'.left ⟶ G.left) (φ₂ : (G2 G').left ⟶ (G2 G).left), IsGrpPullback G' G g φ ∧ IsSquare φ φ₂ ∧ inc'.left ≫ ψ = φ ≫ inc.left ∧ (inc' ⊗ₘ inc').left ≫ ψ₂ = φ₂ ≫ (inc ⊗ₘ inc).left := by
  intro S' T g A G _ _ _ _ inc pr ε A' G' _ _ _ _ inc' pr' ε' ψ ψ₂ hinc hpr hip hpi hinc' hpr' hip' hpi' hψ hsq hεψ
  have hε' : inc' ≫ ε' = inc' := by rw [← hpi', ← Category.assoc, hip', Category.id_comp]
  have key : inc'.left ≫ ψ = inc'.left ≫ ψ ≫ pr.left ≫ inc.left := by
    rw [← Over.comp_left, hpi, ← hεψ, ← Category.assoc, ← Over.comp_left, hε']
  have hipl : inc.left ≫ pr.left = 𝟙 _ := by rw [← Over.comp_left, hip]; rfl
  have hipl' : inc'.left ≫ pr'.left = 𝟙 _ := by rw [← Over.comp_left, hip']; rfl
  have e2' : inc ≫ ε ≫ pr = 𝟙 G := by rw [← hpi, Category.assoc, reassoc_of% hip, hip]
  have e2 : inc.left ≫ ε.left ≫ pr.left = 𝟙 _ := by
    rw [← Over.comp_left, ← Over.comp_left, e2']; rfl
  have e1 : pr'.left ≫ inc'.left ≫ ψ ≫ pr.left = ψ ≫ ε.left ≫ pr.left := by
    rw [← Category.assoc, ← Over.comp_left, hpi', ← Category.assoc, hεψ, Category.assoc]
  have hψp := hψ.1
  refine ⟨inc'.left ≫ ψ ≫ pr.left, (inc' ⊗ₘ inc').left ≫ ψ₂ ≫ (pr ⊗ₘ pr).left, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    key.trans (by simp only [Category.assoc]), ?_⟩
  · have w : (inc'.left ≫ ψ ≫ pr.left) ≫ G.hom = G'.hom ≫ g := by
      rw [Category.assoc, Category.assoc, Over.w pr, hψp.w, ← Category.assoc, Over.w inc']
    refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk _
      (fun s => hψp.lift (s.fst ≫ inc.left) s.snd (by rw [Category.assoc, Over.w inc]; exact s.condition) ≫ pr'.left)
      ?_ ?_ ?_)
    · intro s
      simp only [Category.assoc]
      rw [e1, hψp.lift_fst_assoc, Category.assoc, e2, Category.comp_id]
    · intro s
      rw [Category.assoc, Over.w pr', hψp.lift_snd]
    · intro s m hm1 hm2
      have hm : m ≫ inc'.left = hψp.lift (s.fst ≫ inc.left) s.snd
          (by rw [Category.assoc, Over.w inc]; exact s.condition) := by
        apply hψp.hom_ext
        · rw [hψp.lift_fst, ← hm1, Category.assoc, key]
          simp only [Category.assoc]
        · rw [hψp.lift_snd, Category.assoc, Over.w inc', hm2]
      calc m = m ≫ inc'.left ≫ pr'.left := by rw [hipl', Category.comp_id]
        _ = _ := by rw [← Category.assoc, hm]
  · intro U x y x₀ y₀ hx hy
    have h1 : (x₀ ≫ inc).left = (x ≫ inc').left ≫ ψ := by
      rw [Over.comp_left, hx, Over.comp_left]
      simp only [Category.assoc]
      rw [← key]
    have h2 : (y₀ ≫ inc).left = (y ≫ inc').left ≫ ψ := by
      rw [Over.comp_left, hy, Over.comp_left]
      simp only [Category.assoc]
      rw [← key]
    have hm := hψ.2 U (x ≫ inc') (y ≫ inc') (x₀ ≫ inc) (y₀ ≫ inc) h1 h2
    calc (x₀ * y₀).left = ((x₀ * y₀) ≫ inc).left ≫ pr.left := by
          rw [Over.comp_left, Category.assoc, hipl, Category.comp_id]
      _ = ((x * y) ≫ inc').left ≫ ψ ≫ pr.left := by
          rw [MonObj.mul_comp, MonObj.mul_comp, hm, Category.assoc]
      _ = _ := by rw [Over.comp_left, Category.assoc]
  · simp only [Category.assoc, tensorHom_fst_left, reassoc_of% hsq.1, tensorHom_fst_left_assoc]
  · simp only [Category.assoc, tensorHom_snd_left, reassoc_of% hsq.2, tensorHom_snd_left_assoc]
  · apply Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components
    · simp only [Category.assoc, tensorHom_fst_left, reassoc_of% hsq.1, hsq.1, tensorHom_fst_left_assoc]
      rw [← key]
    · simp only [Category.assoc, tensorHom_snd_left, reassoc_of% hsq.2, hsq.2, tensorHom_snd_left_assoc]
      rw [← key]

end GlobalTheory.ImgPB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageRelationOfPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.UPel.HT

theorem zRel_of_pullback : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₂ act₂ w₁ act₁ y → SiegPB c₂ c₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ := by
  intro h h' M B _ ζ O _ e jl n o κ S₁ S₂ s₁ s₂ y c₁ w₁ act₁ c₂ w₂ act₂ hA hS hZ
  obtain ⟨ψ, ψ₂, hψ, sqψ, hwP, hwl, hact⟩ := hA
  obtain ⟨φ, φ₂, hφ, sqφ, hcP, hcl⟩ := hS
  obtain ⟨inc₁, pr₁, mi₁, mp₁, ip₁, pi₁, hP₁, hl₁, hz₁⟩ := hZ
  haveI := mi₁
  haveI := mp₁
  have wi : (φ ≫ inc₁.left) ≫ w₁.A.hom = c₂.A.hom ≫ y := by
    rw [Category.assoc, Over.w inc₁]; exact hφ.1.w
  let inc₂ : c₂.A ⟶ w₂.A := Over.homMk (hψ.1.lift (φ ≫ inc₁.left) c₂.A.hom wi) (hψ.1.lift_snd _ _ _)
  have inc₂_l : inc₂.left ≫ ψ = φ ≫ inc₁.left := hψ.1.lift_fst _ _ _
  have wp : (ψ ≫ pr₁.left) ≫ c₁.A.hom = w₂.A.hom ≫ y := by
    rw [Category.assoc, Over.w pr₁]; exact hψ.1.w
  let pr₂ : w₂.A ⟶ c₂.A := Over.homMk (hφ.1.lift (ψ ≫ pr₁.left) w₂.A.hom wp) (hφ.1.lift_snd _ _ _)
  have pr₂_l : pr₂.left ≫ φ = ψ ≫ pr₁.left := hφ.1.lift_fst _ _ _
  have extW : ∀ {T : Over S₂} (a b : T ⟶ w₂.A), a.left ≫ ψ = b.left ≫ ψ → a = b := fun a b hab =>
    Over.OverMorphism.ext (hψ.1.hom_ext hab (by rw [Over.w, Over.w]))
  have extC : ∀ {T : Over S₂} (a b : T ⟶ c₂.A), a.left ≫ φ = b.left ≫ φ → a = b := fun a b hab =>
    Over.OverMorphism.ext (hφ.1.hom_ext hab (by rw [Over.w, Over.w]))
  have pI : ∀ (T : Over S₂) (x : T ⟶ c₂.A), pushHom hψ T (x ≫ inc₂) = pushHom hφ T x ≫ inc₁ := fun T x =>
    Over.OverMorphism.ext (by
      show (x ≫ inc₂).left ≫ ψ = (x.left ≫ φ) ≫ inc₁.left
      rw [Over.comp_left, Category.assoc, inc₂_l, Category.assoc])
  have pP : ∀ (T : Over S₂) (x : T ⟶ w₂.A), pushHom hφ T (x ≫ pr₂) = pushHom hψ T x ≫ pr₁ := fun T x =>
    Over.OverMorphism.ext (by
      show (x ≫ pr₂).left ≫ φ = (x.left ≫ ψ) ≫ pr₁.left
      rw [Over.comp_left, Category.assoc, pr₂_l, Category.assoc])
  have mI : IsMonHom inc₂ := isMonHom_of_mul _ fun T x z => extW _ _ (congrArg (fun q => q.left)
    (calc pushHom hψ T ((x * z) ≫ inc₂) = pushHom hφ T (x * z) ≫ inc₁ := pI _ _
      _ = (pushHom hφ T x * pushHom hφ T z) ≫ inc₁ := by rw [map_mul]
      _ = (pushHom hφ T x ≫ inc₁) * (pushHom hφ T z ≫ inc₁) := MonObj.mul_comp _ _ _
      _ = pushHom hψ T (x ≫ inc₂) * pushHom hψ T (z ≫ inc₂) := by rw [pI, pI]
      _ = pushHom hψ T ((x ≫ inc₂) * (z ≫ inc₂)) := (map_mul _ _ _).symm))
  have mP : IsMonHom pr₂ := isMonHom_of_mul _ fun T x z => extC _ _ (congrArg (fun q => q.left)
    (calc pushHom hφ T ((x * z) ≫ pr₂) = pushHom hψ T (x * z) ≫ pr₁ := pP _ _
      _ = (pushHom hψ T x * pushHom hψ T z) ≫ pr₁ := by rw [map_mul]
      _ = (pushHom hψ T x ≫ pr₁) * (pushHom hψ T z ≫ pr₁) := MonObj.mul_comp _ _ _
      _ = pushHom hφ T (x ≫ pr₂) * pushHom hφ T (z ≫ pr₂) := by rw [pP, pP]
      _ = pushHom hφ T ((x ≫ pr₂) * (z ≫ pr₂)) := (map_mul _ _ _).symm))
  have h1 : inc₂ ≫ pr₂ = 𝟙 c₂.A := extC _ _ (by
    rw [Over.comp_left, Over.id_left, Category.assoc, pr₂_l, ← Category.assoc, inc₂_l, Category.assoc,
      ← Over.comp_left, ip₁, Over.id_left, Category.comp_id, Category.id_comp])
  have h2 : pr₂ ≫ inc₂ = act₂ e := extW _ _ (by
    rw [Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, pr₂_l, Category.assoc, ← Over.comp_left, pi₁,
      hact])
  have eι : (inc₂ ⊗ₘ inc₂).left ≫ ψ₂ = φ₂ ≫ (inc₁ ⊗ₘ inc₁).left := by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, sqψ.1, ← Category.assoc, ← Over.comp_left, tensorHom_fst, Category.assoc, ← Over.comp_left,
        tensorHom_fst, Over.comp_left, Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, ← sqφ.1,
        Category.assoc]
    · rw [Category.assoc, sqψ.2, ← Category.assoc, ← Over.comp_left, tensorHom_snd, Category.assoc, ← Over.comp_left,
        tensorHom_snd, Over.comp_left, Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, ← sqφ.2,
        Category.assoc]
  have P1 : LBIso (c₁.P.pull φ₂) (w₁.P.pull (φ₂ ≫ (inc₁ ⊗ₘ inc₁).left)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c₁.P φ₂ φ₂ rfl)
      (chartPullSame w₁.P _ (fun _ => (inc₁ ⊗ₘ inc₁).left) _ φ₂ fun _ => rfl) hP₁
  have P2 : LBIso (w₂.P.pull (inc₂ ⊗ₘ inc₂).left) (w₁.P.pull (φ₂ ≫ (inc₁ ⊗ₘ inc₁).left)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull w₂.P (inc₂ ⊗ₘ inc₂).left (inc₂ ⊗ₘ inc₂).left rfl)
      (chartPullSame w₁.P _ (fun _ => ψ₂) _ (inc₂ ⊗ₘ inc₂).left fun _ => eι.symm) hwP
  have hP₂ : LBIso c₂.P (w₂.P.pull (inc₂ ⊗ₘ inc₂).left) :=
    LBIso.trans c₂.isLB (pull_isLB c₁.isLB _) (pull_isLB w₂.isLB _) hcP
      (LBIso.trans (pull_isLB c₁.isLB _) (pull_isLB w₁.isLB _) (pull_isLB w₂.isLB _) P1 P2.symm)
  have lv : ∀ a, c₂.lev a ≫ inc₂ = w₂.lev (jl a) := fun a => extW _ _ (by
    rw [Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, hcl, Category.assoc, ← Over.comp_left, hl₁, hwl])
  let T₀ : Over S₂ := 𝟙_ (Over S₂)
  let u : Over.mk (T₀.hom ≫ y) ⟶ 𝟙_ (Over S₁) := toUnit _
  have hu : u.left = y := by
    simp [u, T₀]
  have pL : ∀ a, pushHom hψ T₀ (w₂.lev a) = u ≫ w₁.lev a := fun a => Over.OverMorphism.ext (by
    show (w₂.lev a).left ≫ ψ = u.left ≫ (w₁.lev a).left
    rw [hu, hwl])
  have pT : ∀ (b : Fin h ⊕ Fin h → ℤ) (r : O), pushHom hψ T₀ (c₂.lev b ≫ inc₂ ≫ act₂ r) =
      u ≫ (c₁.lev b ≫ inc₁ ≫ act₁ r) := fun b r => Over.OverMorphism.ext (by
    show (c₂.lev b ≫ inc₂ ≫ act₂ r).left ≫ ψ = u.left ≫ (c₁.lev b ≫ inc₁ ≫ act₁ r).left
    simp only [Over.comp_left, Category.assoc]
    rw [hact, reassoc_of% inc₂_l, reassoc_of% (hcl b), hu])
  have lz : ∀ a, w₂.lev a = (List.ofFn fun k => c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k)).prod := fun a =>
    extW _ _ (congrArg (fun q => q.left)
      (calc pushHom hψ T₀ (w₂.lev a) = u ≫ w₁.lev a := pL a
        _ = preHom (G := w₁.A) u (List.ofFn fun k => c₁.lev (κ k a) ≫ inc₁ ≫ act₁ (o k)).prod := by
          rw [hz₁ a]; rfl
        _ = (List.ofFn fun k => u ≫ (c₁.lev (κ k a) ≫ inc₁ ≫ act₁ (o k))).prod := by
          rw [map_list_prod, List.map_ofFn]; rfl
        _ = (List.ofFn fun k => pushHom hψ T₀ (c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k))).prod := by
          simp only [pT]
        _ = pushHom hψ T₀ (List.ofFn fun k => c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k)).prod := by
          rw [map_list_prod, List.map_ofFn]; rfl))
  exact ⟨inc₂, pr₂, mI, mP, h1, h2, hP₂, lv, lz⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldCombinationKillingFunctionsCoeffZeStatement
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
theorem _root_.GlobalTheory.T.invariant_field_combination_killing_functions_coeff_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (W : G.left.Opens) (c : Fin n → Γ(G.left, W)), (∀ O, O ≤ W → ∀ f, ∑ a, rsT (c a) O * dd a O f = 0) → ∀ a, c a = 0 := by
  first | exact @GlobalTheory.InvCoefUniq.coef_eq_zero | exact GlobalTheory.InvCoefUniq.coef_eq_zero | (intros; apply GlobalTheory.InvCoefUniq.coef_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldOfTangentVectorLinearCombinaStatement
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
theorem _root_.GlobalTheory.T.invariant_vectorField_of_tangent_vector_linear_combination : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) G) (e : Fin g → Fld G.left), (∀ c, IsInv G (w c) (e c)) → ∀ a : Fin g → R, IsInv G (∑ c, a c • w c) (fun O f => ∑ c, constFn G.hom O (a c) * e c O f) := by
  first | exact @GlobalTheory.Heat.InvComb.isInv_comb | exact GlobalTheory.Heat.InvComb.isInv_comb | (intros; apply GlobalTheory.Heat.InvComb.isInv_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldPullbackAlongGroupHomStatement
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
theorem _root_.GlobalTheory.T.invariant_vectorField_pullback_along_group_hom : ∀ (R : Type) [CommRing R] (G B : Over (Sp R)) [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B] (q : G ⟶ B) [IsMonHom q] (v : TanM (𝟙 (Sp R)) G) (u : TanM (𝟙 (Sp R)) B) (dd : Fld G.left) (e : Fld B.left), tv v ≫ q = tv u → IsInv G v dd → IsInv B u e → ∀ (V : B.left.Opens) (W : G.left.Opens), W ≤ q.left ⁻¹ᵁ V → ∀ f : Γ(B.left, V), dd W (pbT q.left f W) = pbT q.left (e V f) W := by
  first | exact @GlobalTheory.Heat.PullField.isInv_pbT_single | exact GlobalTheory.Heat.PullField.isInv_pbT_single | (intros; apply GlobalTheory.Heat.PullField.isInv_pbT_single <;> assumption)
end

