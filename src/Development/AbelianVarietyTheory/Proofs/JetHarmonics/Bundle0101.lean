import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.PointDataQ
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0034
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0047
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralExpansionsOfValuationGe
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace IntComb

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)}

theorem exists_int_of_vge (hϖ : Irreducible ϖ) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))} {r : ℚ}
    (hr : 0 ≤ r) (hs : VGe D (FractionRing V) (FamInt.ordVal hϖ) k α s r) :
    ∃ f : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  obtain ⟨n, a, σ, σF, hσ, hva, hsum⟩ := hs
  have hint : ∀ i, ∃ b : V, a i = algebraMap V (FractionRing V) b := fun i => by
    obtain ⟨b, hb⟩ := (FamInt.le_ordFn_iff hϖ (a i) 0).1 (le_trans (by exact_mod_cast hr) (hva i))
    exact ⟨b, by rw [hb, zpow_zero, _root_.one_mul]⟩
  choose b hb using hint
  refine ⟨FamInt.secLin (fun i => scal D.toPre.P.A.hom (b i)) σ,
    SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_⟩
  rw [SectionScalarValuation.sval_lin (fun i => scal D.toPre.P.A.hom (b i)) σ (fun _ => rfl) _ y hJ,
    SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF (fun j => hsum j) (𝟙 _) y hJ]
  refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ (SectionScalarValuation.secScal_sval (hσ i) _ y hJ)
  have e1 : gs (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y ⊤ (scal D.toPre.P.A.hom (b i)) =
      cst ((𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom) y (b i) :=
    gs_pull _ _ y ⊤ trivial _
  have e2 : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (a i)) =
      cst (𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) y (a i) :=
    gs_pull _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial _
  have e3 : (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom =
      ((𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) ≫
        spMap (algebraMap (FractionRing V) (FractionRing V))) ≫ spMap (algebraMap V (FractionRing V)) := by
    rw [Category.id_comp, Category.id_comp, Category.assoc, Over.w]
    exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
  rw [e1, e2, e3, cst_comp, cst_comp, hb i]
  rfl

theorem integralFamily_of_min (hL : Laws) (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {q : ℕ} (hq : 1 ≤ q) (χ : D.toPre.X) (β : D.toPre.SecB q χ) (hmin : ∀ z, Q χ ≤ Q (χ + q • z)) :
    ∃ (Φ : Fam D.toPre (FractionRing V) q) (f : ∀ α, D.toPre.SecB q α),
      (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) (f α) (DegPre.prB D.toPre (FractionRing V)).left 1) ∧
      f χ = β ∧ ∀ α, (∀ z, α ≠ χ + q • z) → ∀ j, (f α).f j = 0 := by
  classical
  obtain ⟨σ, hσ⟩ := FamInt.exists_pull (F := FractionRing V) β
  obtain ⟨Φ, hΦ, hΦ0⟩ := UUA.exists_fam_rep (F := FractionRing V) hL.globalFns D.tau_bimult q χ (fun a b h => by
    have h' : (q : ℤ) • a = (q : ℤ) • b := by
      rw [natCast_zsmul, natCast_zsmul]; exact add_left_cancel h
    exact smul_right_injective D.toPre.X (by omega : (q : ℤ) ≠ 0) h') σ
  have h0 : VGe D (FractionRing V) (FamInt.ordVal hϖ) q χ (Φ.s χ) 0 := by
    refine ⟨1, fun _ => 1, fun _ => β, fun _ => Φ.s χ, fun _ => hΦ ▸ hσ, fun _ => ?_, fun j => ?_⟩
    · simp
    · simp [DegPre.constBF]
  have key : ∀ α : D.toPre.X, ∃ f : D.toPre.SecB q α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) f (DegPre.prB D.toPre (FractionRing V)).left 1 ∧
      (∀ h : χ = α, f = h ▸ β) ∧ ((∀ z, α ≠ χ + q • z) → ∀ j, f.f j = 0) := by
    intro α
    by_cases hα : χ = α
    · subst hα
      exact ⟨β, hΦ ▸ hσ, fun _ => rfl, fun h => absurd (by simp) (h 0)⟩
    by_cases hc : ∃ z, α = χ + q • z
    · obtain ⟨z, rfl⟩ := hc
      have H := SectionScalarValuation.fe_move hϖ hQ (FamInt.valOver_ordVal hϖ) q z χ Φ h0
      have hle := hmin z
      rw [q_shift hϖ hQ, le_add_iff_nonneg_right] at hle
      have hpos : (0 : ℤ) ≤ q * Q z + QForm.bOf D.toPre Q z χ :=
        nonneg_of_mul_nonneg_right hle (by omega)
      obtain ⟨f, h1⟩ := exists_int_of_vge hϖ (by rw [zero_add]; exact_mod_cast hpos) H
      exact ⟨f, h1, fun h => absurd h hα, fun h => absurd rfl (h z)⟩
    · refine ⟨SecOps.secZero, SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_, fun h => absurd h hα,
        fun _ _ => rfl⟩
      rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
        UUA.sval_zero_of (hΦ0 α fun mu e => hc ⟨mu, e.symm⟩) _ y J (hJ.mem _ _)]
  choose f h1 h2 h3 using key
  exact ⟨Φ, f, h1, h2 χ rfl, h3⟩

theorem exists_min_reps (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {q : ℕ} (hq : 1 ≤ q) : ∃ (N : ℕ) (χ : Fin N → D.toPre.X), (∀ α, ∃ i m, α = χ i + q • m) ∧
      (∀ i i', i' ≠ i → ∀ z, χ i ≠ χ i' + q • z) ∧ ∀ i z, Q (χ i) ≤ Q (χ i + q • z) := by
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.toPre.X q hq
  have hnn : ∀ x, 0 ≤ Q x := fun x => by
    by_cases hx : x = 0
    · rw [hx, QForm.Q_zero hϖ D hQ]
    · exact le_trans zero_le_one (QForm.Q_pos hϖ D hQ hx)
  have hm : ∀ i, ∃ m : D.toPre.X, ∀ z, Q (e i + q • m) ≤ Q (e i + q • z) := fun i => by
    refine ⟨Function.argmin (fun z : D.toPre.X => (Q (e i + q • z)).toNat), fun z => ?_⟩
    have h := Function.argmin_le (fun z : D.toPre.X => (Q (e i + q • z)).toNat) z
    have h1 := hnn (e i + q • z)
    omega
  choose m hm using hm
  refine ⟨_, fun i => e i + q • m i, fun α => ?_, fun i i' hi z h => hi ?_, fun i z => ?_⟩
  · obtain ⟨i, ⟨z, hz⟩, -⟩ := he α
    exact ⟨i, z - m i, by rw [hz, smul_sub, add_assoc, add_sub_cancel]⟩
  · exact (he (e i + q • m i)).unique ⟨m i' + z, by rw [smul_add, ← add_assoc]; exact h⟩ ⟨m i, rfl⟩
  · have := hm i (m i + z)
    rwa [smul_add, ← add_assoc] at this

variable {F : Type} [Field F] [Algebra (FractionRing V) F] {k : ℕ}

theorem sum_f {n : ℕ} (S : Finset (Fin n)) (t : Fin n → Fam D.toPre F k) (α : D.toPre.X) (j) :
    ((∑ i ∈ S, t i).s α).f j = ∑ i ∈ S, ((t i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

theorem sval_comb {n : ℕ} (c : Fin n → F) (t : Fin n → Fam D.toPre F k) (α : D.toPre.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J} (hJ : Good D.toPre.P.L z J) :
    sval ((∑ i, c i • t i).s α) r z J =
      ∑ i, gs r z ⊤ (scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)) * sval ((t i).s α) r z J :=
  SectionScalarValuation.sval_lin (fun i => gF D.toPre F (c i)) (fun i => (t i).s α) (fun j => sum_f _ _ α j) r z hJ

end IntComb

theorem exists_integral_expansions_of_vge : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (q : ℕ), 1 ≤ q → ∀ (s : Fam D.toPre F q) (r : ℚ), (∀ χ, VGe D F v q χ (s.s χ) r) → ∃ (l : ℕ) (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (f : Fin l → ∀ α, D.toPre.SecB q α), (∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (c i)) ∧ (∀ i e, U.ExpandsAt e q (σ i) (f i)) ∧ ∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε q) (s.s α) (D.toPre.famφB α) (DegPre.famε q) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)) := by
  intro hL V _ _ _ ϖ hϖ D A G _ _ U Q hQ F _ _ v _ q hq s r hs
  classical
  obtain ⟨N, χ, hrep, hdis, hmin⟩ := IntComb.exists_min_reps hϖ hQ hq
  choose n a β βF hβ hva hsum using fun i => hs (χ i)
  choose Φ f hf hfβ hf0 using fun p : (Σ i : Fin N, Fin (n i)) =>
    IntComb.integralFamily_of_min hL hϖ hQ hq (χ p.1) (β p.1 p.2) (hmin p.1)
  choose σ hσ using fun p => IntegralExpansion.main hL V D A G U q hq (Φ p) (f p) (hf p)
  choose θ hθ using fun p => GlobalTheory.T.integralDegenerationFamily_baseChange_extensionField hL.globalFns V _ D q (Φ p) (f p) (hf p) F
  let E := (Fintype.equivFin (Σ i : Fin N, Fin (n i))).symm
  have hst : s = ∑ x, a (E x).1 (E x).2 • θ (E x) := by
    refine fam_ext fun α => ?_
    obtain ⟨i, m, rfl⟩ := hrep α
    refine fam_eq_on_class_of_eq hL.globalFns V D.toPre F q _ _ (χ i) ?_ m
    refine sec_ext_val D.toPre.P.isLB fun y J hJ => ?_
    rw [IntComb.sval_comb _ _ _ _ _ hJ,
      SectionScalarValuation.sval_lin (fun x => gF D.toPre F (a i x)) (βF i) (fun j => hsum i j) (𝟙 _) y hJ,
      E.sum_comp (fun p => gs (𝟙 _) y ⊤ (scal (fst (TF (R := V) F) D.toPre.P.A).left (a p.1 p.2)) *
        sval ((θ p).s (χ i)) (𝟙 _) y J), Fintype.sum_sigma, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun x _ => congrArg₂ (· * ·) rfl ?_
      rw [← SectionScalarValuation.secScal_sval (hβ i x) _ y hJ, ← SectionScalarValuation.secScal_sval (hθ ⟨i, x⟩ (χ i)) _ y hJ, hfβ ⟨i, x⟩]
    · refine fun i' _ hi => Finset.sum_eq_zero fun x _ => ?_
      rw [← SectionScalarValuation.secScal_sval (hθ ⟨i', x⟩ (χ i)) _ y hJ,
        UUA.sval_zero_of (hf0 ⟨i', x⟩ (χ i) (hdis i i' hi)) _ y J (hJ.mem _ _), mul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  refine ⟨_, fun x => a (E x).1 (E x).2, fun x => σ (E x), fun x => f (E x), fun x => hva _ _,
    fun x e => hσ _ e, fun α => ?_⟩
  refine (FieldBaseChange.secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_
  rw [hst, IntComb.sval_comb _ _ _ _ _ hJ]
  exact Finset.sum_congr rfl fun x _ => by rw [SectionScalarValuation.secScal_sval (hθ _ α) _ _ hJ]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueFrameSer
section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PtGermCompare

theorem surjective_cube {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom := by
  have hG := GlobalTheory.globalFns_holds
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    RigidIsoCube.surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have s₂ := surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg G) s₁
  rw [Over.w (snd G G)] at s₂
  have s₃ := surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg (G ⊗ G)) s₂
  rw [Over.w (snd G (G ⊗ G))] at s₃
  exact s₃

theorem cubical_unique {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (sj : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom) {L : RigLB G} (c c' : CubicalStr G L) : c = c' := by
  let e : 𝟙_ (Over S) ⟶ G3 G := lift 1 (lift 1 1)
  have h : c.t.s = c'.t.s := JetSer.gen_ext_val L.isLB (φ := thφ G (x3 G)) (ε := thε) c.isGen c'.isGen fun y J hJ =>
    gen_unique L.isLB (φ := thφ G (x3 G)) (ε := thε) (G3 G).hom e.left (Over.w e) sj c.isGen c'.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV c' hJ).face 1 1).symm) _ _ y J hJ
  obtain ⟨⟨t⟩, _⟩ := c
  obtain ⟨⟨t'⟩, _⟩ := c'
  obtain rfl : t = t' := h
  rfl

theorem cub_heq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R]
    {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) : HEq P.U.cubG t.cub := by
  have key : ∀ (L L' : RigLB t.G) (_ : L = L') (c : CubicalStr t.G L) (c' : CubicalStr t.G L'), HEq c c' := by
    rintro L _ rfl c c'
    exact heq_of_eq (cubical_unique (surjective_cube P.U.toUnifPre) c c')
  exact key _ _ P.bundle _ _

section Scale
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))}

def constUnit (G : Over (Spec (CommRingCat.of R))) (c : Rˣ) : Γ(G.left, ⊤)ˣ :=
  Units.map (G.hom.appTop.hom : _ →* _) (unitOn c)

def constMul {M : LB G.left} (c : Rˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun j => res le_top (constUnit G c) * t.s j⟩

theorem constMul_isGen {M : LB G.left} (c : Rˣ) {t : LB.Gen M} (ht : t.IsGen) : (constMul c t).IsGen := by
  intro i j
  have e : ∀ {U W : G.left.Opens} (h : W ≤ U) (a : Γ(G.left, ⊤)ˣ), res h (res le_top a) = res le_top a :=
    fun h a => Units.ext (SecOps.resTop_res h a.val)
  simp only [constMul, map_mul, e]
  rw [ht i j, mul_left_comm]

end Scale

section Bound
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}

end Bound

section Cast
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {L L' : RigLB G}

def castIdx (h : L = L') (j : L.L.ι) : L'.L.ι := Eq.rec (motive := fun M _ => M.L.ι) j h

def castGen (h : L = L') {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ G.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L.L φ ε)) : LB.Gen (LB.LinComb L'.L φ ε) :=
  Eq.rec (motive := fun M _ => LB.Gen (LB.LinComb M.L φ ε)) t h

theorem castIdx_castIdx (h : L = L') (h' : L' = L) (j : L.L.ι) : castIdx h' (castIdx h j) = j := by subst h; rfl

theorem castGen_castGen (h : L = L') (h' : L' = L) {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ G.left)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L.L φ ε)) : castGen h' (castGen h t) = t := by subst h; rfl

theorem cast_unit (h : L = L') {j : L.L.ι} (hj : ⊤ ≤ η[G].left ⁻¹ᵁ L.L.U j) :
    ⊤ ≤ η[G].left ⁻¹ᵁ L'.L.U (castIdx h j) := by subst h; exact hj

theorem cast_isGen (h : L = L') {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ G.left)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L.L φ ε)} (ht : t.IsGen) : (castGen h t).IsGen := by subst h; exact ht

theorem cast_normRos (h : L = L') {f g : G ⟶ G} {u : LB.Gen (LB.LinComb L.L (rosatiφ G f g) rosatiε)}
    (hu : JetSer.IsNormRos L.L f g u) : JetSer.IsNormRos L'.L f g (castGen h u) := by subst h; exact hu

theorem cast_rig (h : L = L') {w : G ⟶ G} {ρ : LB.Gen (LB.LinComb L.L (JetSer.primφ w) JetSer.primε)}
    (hρ : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ ρ (eSec G)) L.rig) :
    LB.Gen.Corr L'.L _ _ _ _ (LB.pullGen L'.L _ _ (castGen h ρ) (eSec G)) L'.rig := by subst h; exact hρ

theorem cast_isFBOf (h : L = L') {c : CubicalStr G L} {c' : CubicalStr G L'} (hc : HEq c c') {O : Type} [CommRing O]
    [StarRing O] {act : OAct O G}
    {u : ∀ a : O, LB.Gen (LB.LinComb L.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)} {d : ℕ}
    {x : JetSer.Fam G (Fin d)} {j : L.L.ι} {B : FB R d O} (hB : JetSer.IsFBOf L c act u x j B) :
    JetSer.IsFBOf L' c' act (fun a => castGen h (u a)) x (castIdx h j) B := by
  subst h; cases hc; exact hB

end Cast

open GlobalTheory.FamGerm GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData

section Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [Algebra (FractionRing V) F]

def Rigid (y : Pt1 E H V F) : Prop :=
  LB.Gen.Corr y.P.U.LG.L _ _ _ _ (LB.pullGen y.P.U.LG.L _ _ y.ρ (eSec y.t.G)) y.P.U.LG.rig

def rescale (y : Pt1 E H V F) (c : Vˣ) : Pt1 E H V F :=
  { y with ρ := constMul c y.ρ, hρ := constMul_isGen c y.hρ }

variable [CharZero F]

def toPt {t : SAB H (Sp V)} {P : PELUnif (maximalIdeal V) t} (D : PtData P F) : Pt1 E H V F where
  ϖ := D.ϖ
  hϖ := D.irr
  complete := D.complete
  t := t
  P := P
  tors := D.tors
  Q := D.Q_vw
  hQ := D.isQ
  v := D.v_vw
  hv := D.valOver
  d := D.d
  x := D.x
  hx := D.chart
  j := castIdx P.bundle.symm D.j
  hj := cast_unit _ D.hj
  u := fun a => castGen P.bundle.symm (D.u a)
  hu := fun a => cast_normRos _ (D.u_norm a)
  B := D.B
  hB := letI := H.starRing; cast_isFBOf P.bundle.symm (cub_heq P).symm D.isFB
  ρ := castGen P.bundle.symm D.ρ
  hρ := cast_isGen _ D.ρ_gen

theorem rigid_toPt {t : SAB H (Sp V)} {P : PELUnif (maximalIdeal V) t} (D : PtData P F) : Rigid (toPt D) :=
  cast_rig P.bundle.symm D.ρ_rig

def ofPt (hF : IsAlgClosed F) (y : Pt1 E H V F) (hy : Rigid y) : PtData y.P F where
  complete := y.complete
  tors := y.tors
  ϖ := y.ϖ
  irr := y.hϖ
  Q_vw := y.Q
  isQ := y.hQ
  algClosed := hF
  v_vw := y.v
  valOver := y.hv
  d := y.d
  x := y.x
  chart := y.hx
  j := castIdx y.P.bundle y.j
  hj := cast_unit _ y.hj
  u := fun a => castGen y.P.bundle (y.u a)
  u_norm := fun a => cast_normRos _ (y.hu a)
  ρ := castGen y.P.bundle y.ρ
  ρ_gen := cast_isGen _ y.hρ
  ρ_rig := cast_rig y.P.bundle hy
  B := y.B
  isFB := letI := H.starRing; cast_isFBOf y.P.bundle (cub_heq y.P) y.hB

theorem ofPt_toPt (hF : IsAlgClosed F) {t : SAB H (Sp V)} {P : PELUnif (maximalIdeal V) t} (D : PtData P F) :
    ofPt hF (toPt D) (rigid_toPt D) = D := by
  cases D
  dsimp only [ofPt, toPt]
  congr 1
  exacts [castIdx_castIdx _ _ _, funext fun a => castGen_castGen _ _ _, castGen_castGen _ _ _]

theorem toPt_ofPt (hF : IsAlgClosed F) (y : Pt1 E H V F) (hy : Rigid y) : toPt (ofPt hF y hy) = y := by
  cases y
  simp only [ofPt, toPt, castIdx_castIdx, castGen_castGen]

def ptEquiv (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F]
    [Algebra (FractionRing V) F] [CharZero F] (hF : IsAlgClosed F) :
    (Σ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), PtData P F) ≃ {y : Pt1 E H V F // Rigid y} where
  toFun X := ⟨toPt X.2.2, rigid_toPt _⟩
  invFun y := ⟨y.1.t, y.1.P, ofPt hF y.1 y.2⟩
  left_inv X := congrArg (fun D => (⟨X.1, X.2.1, D⟩ : Σ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), PtData P F))
    (ofPt_toPt hF X.2.2)
  right_inv y := Subtype.ext (toPt_ofPt hF y.1 y.2)

end Data

section Statements

def GermValMinSt_vw : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (F : Type) [Field F] [CharZero F] [Algebra (FractionRing V) F] (D : PtData P F) (q : ℕ), 1 ≤ q →
    ∀ (s : Fam P.D.toPre F q) (f : PS F 1 D.d), D.IsGerm q s f → ∀ r : ℚ,
      ((∀ χ, VGe P.D F D.v_vw q χ (s.s χ) r) →
        ∀ a, ((r : ℚ) : WithTop ℚ) ≤ D.v_vw (MvPowerSeries.coeff a f)) ∧
      ∀ (χ₀ : P.D.toPre.X) (y : F), Val0 P.D F q χ₀ (s.s χ₀) y →
        (∀ χ, χ ≠ χ₀ → ∃ r' : ℚ, r < r' ∧ VGe P.D F D.v_vw q χ (s.s χ) r') →
          D.v_vw y = ((r : ℚ) : WithTop ℚ) → D.v_vw (MvPowerSeries.constantCoeff f) = ((r : ℚ) : WithTop ℚ)

def GermCongrSt_vw : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (F : Type) [Field F] [CharZero F] [Algebra (FractionRing V) F] (D : PtData P F) (q : ℕ), 1 ≤ q →
    ∀ (s : Fam P.D.toPre F q) (f : PS F 1 D.d), D.IsGerm q s f → ∀ r : ℚ,
      ∀ (χ₀ : P.D.toPre.X) (y : F), Val0 P.D F q χ₀ (s.s χ₀) y →
        (∀ χ, χ ≠ χ₀ → ∃ r' : ℚ, r < r' ∧ VGe P.D F D.v_vw q χ (s.s χ) r') →
        ((r : ℚ) : WithTop ℚ) < D.v_vw (MvPowerSeries.constantCoeff f - y)

def PtExCharZeroSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (F : Type) [Field F]
    [Algebra (FractionRing V) F] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ v : AddValuation F (WithTop ℚ), ValOver ϖ F v →
    ∃ y : Pt1 E H V F, y.t = t ∧ HEq y.P P ∧ y.v = v ∧ y.ϖ = ϖ

end Statements

end GlobalTheory.PtGermCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowOActOfGlobalFns
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem powOAct_of_globalFns : GlobalFnsSt → PowOActSt := by
  intro hG E _ _ _ H V _ _ _ t P n D' pD
  letI := H.starRing
  letI M : Module (𝓞 E) D'.toPre.X := pD.xe.module (𝓞 E)
  have h : ∀ (a : 𝓞 E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x := by
    intro a x
    exact pD.xe.apply_symm_apply _
  obtain ⟨oa', hoa'⟩ := powDeg_diagonal_action hG V n P.D.toPre D'.toPre pD (𝓞 E) h P.oD
  exact ⟨M, oa', fun a x i => by rw [h]; rfl, hoa'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentTransferStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_moment_transfer : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → Function.Injective muI → TensRaw ρ R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∫ x, ⟪BI I ((RI I).σ (Matrix.of x) y), Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = β I * ⟪y, ∑ c, pr I c (tm R a w c)⟫_ℂ := by
  first | exact @GlobalTheory.BesselPairing.pairing | exact GlobalTheory.BesselPairing.pairing | (intros; apply GlobalTheory.BesselPairing.pairing <;> assumption)
end

