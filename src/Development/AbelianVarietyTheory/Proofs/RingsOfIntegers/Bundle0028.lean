import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0026
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0008
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0020
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SectionsPowerTwistBasisStableBaseChange
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSectionsOfNonzeroSpecial
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NonzeroClosedFibre

theorem exists_restrict {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (h : Y ⟶ X) (k : ℤ)
    (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => k))) :
    ∃ s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => k)),
      GeneratorPullback.SecScal L (fun _ : Fin 1 => h) (fun _ => k) s (fun _ : Fin 1 => 𝟙 X) (fun _ => k) σ h 1 := by
  have key : ∀ φ' : Fin 1 → (Y ⟶ X), (fun _ : Fin 1 => h ≫ 𝟙 X) = φ' →
      ∃ s : LB.Sec (LB.LinComb L φ' (fun _ => k)),
        GeneratorPullback.SecScal L φ' (fun _ => k) s (fun _ : Fin 1 => 𝟙 X) (fun _ => k) σ h 1 := by
    rintro _ rfl
    refine ⟨DVR.pullSec L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) σ h,
      SectionScalarValuation.secScal_of_sval hL fun y J hJ => ?_⟩
    exact (SectionScalarValuation.sval_pullSec _ _ σ h _ y hJ).symm
  exact key _ (funext fun _ => Category.comp_id h)

theorem secIsMul_of_vge {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) {k : ℕ} {χ : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))} {g : D.toPre.SecB k χ}
    (hg : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) s (D.toPre.famφB χ)
      (DegPre.famε k) g (DegPre.prB D.toPre F).left 1) {r : ℚ} (hr : 0 < r) (hs : VGe D F v k χ s r) :
    ∃ g' : D.toPre.SecB k χ, SecIsMul D.toPre.P.A.hom ϖ g g' := by
  obtain ⟨n, a₀, τ, τF, hτ, hva, hsum⟩ := hs
  have hb : ∀ i, 0 < v (a₀ i) := fun i => lt_of_lt_of_le (by exact_mod_cast hr) (hva i)
  have vc : ∀ (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))) (x : F)
      {Z : Scheme.{0}} (q : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (j), q z ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j →
      gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (DegPre.constBF D.toPre F x _ * t.f j) =
        cst (q ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z x *
          gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (t.f j) := fun t x Z q z j hz =>
    (gs_mul q z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res q z le_top hz _).trans
      (gs_pull q (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _)) rfl)
  have div₁ := H1.dvd_of_comb hϖ D.toPre F v hv g τ a₀ hb (fun Z q z J hJ =>
    (H1.sval_scal hg q z hJ).symm.trans
      ((congrArg (gs _ z _) (hsum _)).trans ((H1.gs_sum q z _ (hJ.mem _ q) _).trans (Finset.sum_congr rfl fun i _ =>
        (vc (τF i) (a₀ i) q z _ (hJ.mem _ q)).trans (congrArg₂ (· * ·) rfl (H1.sval_scal (hτ i) q z hJ))))))
  have := D.toPre.P.isAb.smooth
  exact exists_div_sec D.toPre.P.A.hom hϖ.ne_zero g div₁

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (ϑ : H0 U.LG.L 1), NonzeroOnSpecial U ϑ → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB 1 α, (∀ e, U.ExpandsAt e 1 ϑ g) ∧ (¬ ∃ σ' : D.toPre.SecB 1 0, ∀ j, (g 0).f j = Geo.Tor.constFn D.toPre.P.A.hom _ ϖ * σ'.f j) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∃ θ : Fam D.toPre F 1, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε 1) (θ.s α) (D.toPre.famφB α) (DegPre.famε 1) (g α) (DegPre.prB D.toPre F).left 1) ∧ NuGe D Q F v 1 θ 0 ∧ ¬ ∃ r : ℚ, 0 < r ∧ NuGe D Q F v 1 θ r := by
  intro hG V _ _ _ ϖ hϖ D Q hQ A G _ _ U ϑ hϑ
  obtain ⟨s, hs⟩ := exists_restrict U.LG.isLB (pullback.fst G.hom (jK V)) ((1 : ℕ) : ℤ) ϑ
  obtain ⟨E, hE, -⟩ := (U.expand 1 le_rfl).1 s
  obtain ⟨g, hexp, hgE⟩ := GlobalTheory.T.expansion_of_integral_section_is_integral V ϖ hϖ D A G U.toUnifPre 1 ϑ s hs E hE
  have hdiv := (GlobalTheory.integralFamily_levelOne V ϖ hϖ D Q hQ (FractionRing V) (GlobalTheory.FamInt.ordVal hϖ)
    (GlobalTheory.FamInt.valOver_ordVal hϖ) E g hgE).2
  have hind : ¬ ∃ g' : D.toPre.SecB 1 0, SecIsMul D.toPre.P.A.hom ϖ (g 0) g' :=
    (GlobalTheory.ClosedFibreTerm.main V ϖ hϖ D A G U.toUnifPre ϑ g (hexp 0) hdiv).1 hϑ
  refine ⟨g, hexp, hind, fun F _ _ v hv => ?_⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.integralDegenerationFamily_baseChange_extensionField hG V (maximalIdeal V) D 1 E g hgE F
  refine ⟨θ, hθ, (GlobalTheory.integralFamily_levelOne V ϖ hϖ D Q hQ F v hv θ g hθ).1, ?_⟩
  rintro ⟨r, hr, hν⟩
  refine hind (secIsMul_of_vge hϖ D F v hv (hθ 0) ?_ (hν 0))
  rw [QForm.Q_zero hϖ D hQ]
  simpa using hr

end GlobalTheory.NonzeroClosedFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionIntegralSectionIntegralNoetherianLocalStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.expansion_integralSection_integral_noetherianLocal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ maximalIdeal R → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (σ : H0 U.LG.L k) (s : U.SecK k), GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK R)) 1 → ∀ E : Fam D.toPre (FractionRing R) k, U.Expands k s E → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB k α, (∀ e, U.ExpandsAt e k σ g) ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
  first | exact @GlobalTheory.IntegralExpansionLocal.main | exact GlobalTheory.IntegralExpansionLocal.main | (intros; apply GlobalTheory.IntegralExpansionLocal.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsBoxSecKOfPull
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericBoxSpan

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange GlobalTheory.BoxExpansion

section General

variable {X X' Γ Γ' Y Y' E E' : Scheme.{0}} {L : LB X} {L' : LB X'} {M : LB Γ} {M' : LB Γ'}
  {f₁ : Y ⟶ X} {f₂ : Y ⟶ Γ}

def Moves (w : LB.Iso (L.pull f₁) (M.pull f₂)) (k : ℕ) {g : E ⟶ X} (h : Y ⟶ E)
    (t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => (k : ℤ))))
    (s : LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J I), Good L z J → Good M z I →
    sval s r z I = (pw w r z (J (r ≫ f₁)) (I (r ≫ f₂)) ^ k).val * sval t (r ≫ h) z J

theorem exists_moves (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull f₁) (M.pull f₂)} (hw : w.IsGen) (k : ℕ)
    {g : E ⟶ X} (h : Y ⟶ E) (e : h ≫ g = f₁) (n : E ⟶ Y) (hn : n ≫ h = 𝟙 _) (hn' : h ≫ n = 𝟙 _) :
    (∀ t, ∃ s, Moves w k (g := g) h t s) ∧ ∀ s, ∃ t, Moves w k (g := g) h t s := by
  have key : ∀ g₂ : Y ⟶ Γ, 𝟙 Y ≫ f₂ = g₂ →
      (∀ a, ∃ b, GeneratorPullback.IsoRelM L M f₁ f₂ w (𝟙 Y) k g h a g₂ (𝟙 _) b) ∧
      ∀ b, ∃ a, GeneratorPullback.IsoRelM L M f₁ f₂ w (𝟙 Y) k g h a g₂ (𝟙 _) b := by
    rintro _ rfl
    obtain ⟨i₁, i₂⟩ := isoRelM_bijective (k := k) (m := 𝟙 Y) (g₁ := g) (h₁ := h) hL hM hw
      (e.trans (Category.id_comp _).symm) n hn hn'
    exact ⟨fun a => (i₁ a).exists, fun b => (i₂ b).exists⟩
  obtain ⟨i₁, i₂⟩ := key f₂ (Category.id_comp _)
  have val : ∀ a b, GeneratorPullback.IsoRelM L M f₁ f₂ w (𝟙 Y) k g h a f₂ (𝟙 _) b → Moves w k h a b := by
    intro a b H Z r z J I hJ hI
    have := isoRel_val H r z hJ hI
    simpa only [Category.comp_id] using this
  exact ⟨fun t => (i₁ t).imp fun s hs => val _ _ hs, fun s => (i₂ s).imp fun t ht => val _ _ ht⟩

variable {j : ℕ} {pr : Fin j → (X' ⟶ X)} {qr : Fin j → (Γ' ⟶ Γ)} {f₁' : Y' ⟶ X'} {f₂' : Y' ⟶ Γ'}
  {ρ : Fin j → (Y' ⟶ Y)}

theorem comb_box {F : Type} [CommRing F] (hL : L.IsLB) (hL' : L'.IsLB) (hM : M.IsLB) (hM' : M'.IsLB)
    (e₁ : ∀ i, f₁' ≫ pr i = ρ i ≫ f₁) (e₂ : ∀ i, f₂' ≫ qr i = ρ i ≫ f₂)
    (wA : LB.Iso L' (LB.LinComb L pr (fun _ => 1))) (wL : LB.Iso M' (LB.LinComb M qr (fun _ => 1)))
    (w : LB.Iso (L.pull f₁) (M.pull f₂)) (w' : LB.Iso (L'.pull f₁') (M'.pull f₂')) (u : Γ(Y', ⊤)ˣ)
    (hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (a : Fin j → L.ι) (a' : L'.ι) (b : Fin j → M.ι) (b' : M'.ι),
      (∀ i, pr i (f₁' (r z)) ∈ L.U (a i)) → f₁' (r z) ∈ L'.U a' → (∀ i, qr i (f₂' (r z)) ∈ M.U (b i)) →
      f₂' (r z) ∈ M'.U b' →
      bw wL (r ≫ f₂') z b b' * pw w' r z a' b' =
        gm r z ⊤ u * ((∏ i, pw w (r ≫ ρ i) z (a i) (b i)) * bw wA (r ≫ f₁') z a a'))
    {k : ℕ} {g : E ⟶ X} {g' : E' ⟶ X'} {h : Y ⟶ E} {h' : Y' ⟶ E'} {κ : Fin j → (E' ⟶ E)}
    {π : E' ⟶ Spec (CommRingCat.of F)} {π' : Y' ⟶ Spec (CommRingCat.of F)}
    (e₄ : ∀ i, h' ≫ κ i = ρ i ≫ h) (e₅ : h' ≫ g' = f₁') (e₆ : h' ≫ π = π') (C : F) (hC : u.val = scal π' C)
    {n : ℕ} (c : Fin n → F)
    (t : Fin n → Fin j → LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => (k : ℤ))))
    (t' : Fin n → LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => g') (fun _ => (k : ℤ))))
    (t₀ : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => g') (fun _ => (k : ℤ))))
    (ht : ∀ l (y : Y') J J', Good L y J → Good L' y J' →
      (bw wA (h' ≫ g') y (fun i => J ((h' ≫ g') ≫ pr i)) (J' (h' ≫ g')) ^ k).val * sval (t' l) h' y J' =
        ∏ i, sval (t l i) (h' ≫ κ i) y J)
    (ht₀ : ∀ jj, t₀.f jj = ∑ l, resTop _ (scal π (c l)) * (t' l).f jj)
    (s : Fin n → Fin j → LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))))
    (s' : Fin n → LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => f₂') (fun _ => (k : ℤ))))
    (s₀ : LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => f₂') (fun _ => (k : ℤ))))
    (hs : ∀ l, BoxFamily.IsBoxPull wL ρ (fun i _ => e₂ i) (s' l) (s l))
    (m : ∀ l i, Moves w k h (t l i) (s l i)) (m₀ : Moves w' k h' t₀ s₀) (jj) :
    s₀.f jj = ∑ l, resTop _ (scal π' (c l * C ^ k)) * (s' l).f jj := by
  obtain ⟨s₁, hs₁⟩ := GenericSectionBasis.exists_comb π' s' (fun l => c l * C ^ k)
  refine (sec_ext_val hM' (s := s₀) (s' := s₁) (fun y I' hI' => ?_) jj).trans (hs₁ jj)
  obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at hL y
  obtain ⟨J', hJ'⟩ := BoxFamily.exists_good_at hL' y
  obtain ⟨I, hI⟩ := BoxFamily.exists_good_at hM y
  have a₀ := hu _ (𝟙 Y') y (fun i => J (f₁' ≫ pr i)) (J' f₁') (fun i => I (f₂' ≫ qr i))
    (I' f₂') (fun i => hJ (f₁' ≫ pr i)) (hJ' f₁') (fun i => hI (f₂' ≫ qr i)) (hI' f₂')
  have a₁ := fun l => ht l y J J' hJ hJ'
  have a₂ := fun l => BoxFamily.boxPull_val (hs l) (𝟙 Y') y hI hI'
  have a₃ := fun l i => m l i _ (ρ i) y J I hJ hI
  have a₄ := m₀ _ (𝟙 Y') y J' I' hJ' hI'
  have a₅ : sval t₀ h' y J' = ∑ l, constHomVal π' y (c l) * sval (t' l) h' y J' := by
    refine (congrArg (gs h' y _) (ht₀ _)).trans
      ((GenericSectionBasis.gs_comb π t' c h' y _ (hJ'.mem _ h')).trans (Finset.sum_congr rfl fun l _ => ?_))
    rw [e₆, ← constVal_eq]
    rfl
  have a₆ : sval s₁ (𝟙 Y') y I' = ∑ l, constHomVal π' y (c l * C ^ k) * sval (s' l) (𝟙 Y') y I' := by
    refine (congrArg (gs (𝟙 Y') y _) (hs₁ _)).trans
      ((GenericSectionBasis.gs_comb π' s' _ (𝟙 Y') y _ (hI'.mem _ (𝟙 Y'))).trans
        (Finset.sum_congr rfl fun l _ => ?_))
    rw [Category.id_comp, ← constVal_eq]
    rfl
  have a₇ : (gm (𝟙 Y') y ⊤ u).val = constHomVal π' y C := by
    rw [← gs_unit _ y ⊤ trivial, hC, gs_scal, Category.id_comp, constVal_eq]
  simp only [Category.id_comp, BoxFamily.om, Fin.prod_univ_one, zpow_natCast, e₅, e₄, ← e₁, ← e₂] at a₀ a₁ a₂ a₃ a₄
  rw [a₄, a₅, a₆, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_pow, ← a₇, mul_left_comm, _root_.mul_assoc]
  refine congrArg _ ?_
  refine (Units.mul_right_inj (bw wL f₂' y (fun i => I (f₂' ≫ qr i)) (I' f₂') ^ k)).1 ?_
  rw [mul_left_comm _ (_ ^ k), a₂ l, ← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, a₀, mul_pow, mul_pow,
    Units.val_mul, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, a₁ l, ← Finset.prod_pow, Units.coe_prod,
    ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun i _ => a₃ l i, Units.val_pow_eq_pow_val]

end General

theorem isBoxSecK_of_pull {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {G G' : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {LG : LB G.left} {LG' : LB G'.left}
    (pG : IsPowGrp G' G j) (w : LB.Iso LG' (boxLB LG pG.pr)) (k : ℕ)
    (s' : LB.Sec (LB.LinComb LG' (K := Fin 1) (fun _ => pullback.fst G'.hom (jK R)) (fun _ => (k : ℤ))))
    (s : Fin j → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))))
    (H : BoxFamily.IsBoxPull (pr := fun i => (pG.pr i).left) w (prK pG) (fun i _ => (prK_fst pG i).symm) s' s) :
    IsBoxSecK pG w k s' s := by
  intro jN jL
  refine fn_ext fun y hy => ?_
  have hm : (𝟙 (pullback G'.hom (jK R)) : _ ⟶ _) y ∈
      LB.wchart (LB.LinComb LG (fun i => (pG.pr i).left) (fun _ => 1)) (fun _ : Fin 1 => pullback.fst G'.hom (jK R))
        (fun _ => jN) ⊓ LB.wchart LG' (fun _ : Fin 1 => pullback.fst G'.hom (jK R)) (fun _ => jL) :=
    ⟨Set.mem_iInter.2 fun _ => hy.1, Set.mem_iInter.2 fun _ => hy.2⟩
  have E := congrArg (gs (𝟙 _) y _) (H (fun _ => jN) (fun _ => jL))
  have E₁ := ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hm _).trans (congrArg Units.val
    (gm_linCombIso w _ _ _ y _ _ hm))) (gs_res _ y _ hm _))).symm.trans (E.trans ((gs_prod _ y _ hm _ _).trans
    (Finset.prod_congr rfl fun i _ => gs_res _ y _ hm _)))
  rw [Fin.prod_univ_one, zpow_natCast] at E₁
  refine ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val
    ((map_pow _ _ _).trans (congrArg (· ^ k) (gm_pull _ _ y _ hy _))))) (gs_res _ y _ hy _))).trans
    (E₁.trans ((gs_prod _ y _ hy _ _).trans (Finset.prod_congr rfl fun i _ => gs_res _ y _ hy _)).symm)

set_option maxHeartbeats 1000000 in

theorem main : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : UnifPre I D' A' G') (U : UnifPre I D A G) (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) → ∀ (k : ℕ), 1 ≤ k → (∀ s : Fin j → U.SecK k, ∃ s' : U'.SecK k, IsBoxSecK pG wL k s' s) ∧ ∀ s₀ : U'.SecK k, ∃ (n : ℕ) (c : Fin n → FractionRing R) (s : Fin n → Fin j → U.SecK k) (s' : Fin n → U'.SecK k), (∀ l, IsBoxSecK pG wL k (s' l) (s l)) ∧ ∀ jj, s₀.f jj = ∑ l, resTop _ (scal (pullback.snd G'.hom (jK R)) (c l)) * (s' l).f jj := by
  intro hL R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U wL hyp k hk
  obtain ⟨hgen, hwL, -⟩ := hyp
  have ex : ∀ s : Fin j → U.SecK k, ∃ s' : U'.SecK k, BoxFamily.IsBoxPull (pr := fun i => (pG.pr i).left) wL (prK pG)
      (fun i _ => (prK_fst pG i).symm) s' s := fun s =>
    BoxFamily.exists_boxPull wL hwL U.LG.isLB U'.LG.isLB _ _ s
  refine ⟨fun s => (ex s).imp fun s' hs' => isBoxSecK_of_pull pG wL k s' s hs', fun s₀ => ?_⟩
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨w', hw'⟩ := U'.ext
  have e₁ : ∀ i, U'.gen.hom.left ≫ (pA.pr i).left = prK pG i ≫ U.gen.hom.left := fun i =>
    congrArg (fun q => q.left) (hgen i)
  have e₂ : ∀ i, pullback.fst G'.hom (jK R) ≫ (pG.pr i).left = prK pG i ≫ pullback.fst G.hom (jK R) := fun i =>
    (prK_fst pG i).symm
  obtain ⟨u, hu⟩ := exists_ratio A.isLB A'.isLB U.LG.isLB U'.LG.isLB e₁ e₂ pA.w_gen hwL hw hw'
  obtain ⟨c₀, -, huc⟩ := unit_const hL.globalFns A' U'.gen u
  have hid : jFK (R := R) (FractionRing R) = 𝟙 _ := Spec.map_id _
  let T := TFK (R := R) (FractionRing R)
  let a : ∀ Y : Over (TK R).left, Y ⟶ T := fun Y => Over.homMk Y.hom (by
    show Y.hom ≫ jFK (R := R) (FractionRing R) = Y.hom
    rw [hid]; exact Category.comp_id _)
  have ha : ∀ (Y : Over (TK R).left) (b : Y ⟶ T), b = a Y := fun Y b => Over.OverMorphism.ext (by
    have := Over.w b
    have e : b.left ≫ jFK (R := R) (FractionRing R) = b.left := by rw [hid]; exact Category.comp_id _
    exact e.symm.trans this)
  have hu₂ : ∀ (Y : Over (TK R).left) (b b' : Y ⟶ T), b = b' := fun Y b b' => (ha Y b).trans (ha Y b').symm
  have mv := exists_moves A.isLB U.LG.isLB hw k (g := (snd T A.A).left) (lift (a _) U.gen.hom).left
    (congrArg (fun q => q.left) (lift_snd (a _) U.gen.hom)) (snd T A.A ≫ U.gen.inv).left
    (congrArg (fun q => q.left) (show (snd T A.A ≫ U.gen.inv) ≫ lift (a _) U.gen.hom = 𝟙 _ from
      CartesianMonoidalCategory.hom_ext _ _ (hu₂ _ _ _) (by simp)))
    (congrArg (fun q => q.left) (show lift (a _) U.gen.hom ≫ (snd T A.A ≫ U.gen.inv) = 𝟙 _ by simp))
  have mv' := exists_moves A'.isLB U'.LG.isLB hw' k (g := (snd T A'.A).left) (lift (a _) U'.gen.hom).left
    (congrArg (fun q => q.left) (lift_snd (a _) U'.gen.hom)) (snd T A'.A ≫ U'.gen.inv).left
    (congrArg (fun q => q.left) (show (snd T A'.A ≫ U'.gen.inv) ≫ lift (a _) U'.gen.hom = 𝟙 _ from
      CartesianMonoidalCategory.hom_ext _ _ (hu₂ _ _ _) (by simp)))
    (congrArg (fun q => q.left) (show lift (a _) U'.gen.hom ≫ (snd T A'.A ≫ U'.gen.inv) = 𝟙 _ by simp))
  obtain ⟨t₀, m₀⟩ := mv'.2 s₀
  obtain ⟨n, c, t, t', ht, ht₀⟩ := boxProduct_span hL R j A A' pA (FractionRing R) k hk t₀
  choose s m using fun l i => mv.1 (t l i)
  choose s' hs using fun l => ex (s l)
  refine ⟨n, fun l => c l * c₀ ^ k, s, s', fun l => isBoxSecK_of_pull pG wL k _ _ (hs l), ?_⟩
  refine comb_box A.isLB A'.isLB U.LG.isLB U'.LG.isLB e₁ e₂ pA.w wL w w' u hu
    (κ := fun i => (T ◁ pA.pr i).left) (π := (fst T A'.A).left) (fun i => ?_)
    (congrArg (fun q => q.left) (lift_snd (a _) U'.gen.hom))
    (congrArg (fun q => q.left) (lift_fst (a _) U'.gen.hom)) c₀ huc c t t' t₀
    (fun l y J J' hJ hJ' => ht l _ _ y J J' hJ hJ') ht₀ s s' s₀ hs m m₀
  refine congrArg (fun q => q.left) (?_ : lift (a _) U'.gen.hom ≫ T ◁ pA.pr i =
    (Over.pullback (jK R)).map (pG.pr i) ≫ lift (a _) U.gen.hom)
  exact CartesianMonoidalCategory.hom_ext _ _ (hu₂ _ _ _) (by simp [hgen])

end GlobalTheory.GenericBoxSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsUnitOfGenerates
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaNu

theorem dvd_of_vGe {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (k : ℕ) (χ : D.toPre.X)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))) (g : D.toPre.SecB k χ)
    (hg : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) s (D.toPre.famφB χ) (DegPre.famε k) g
      (DegPre.prB D.toPre F).left 1) {r : ℚ} (hr : 0 < r) (h : VGe D F v k χ s r) :
    ∃ g' : D.toPre.SecB k χ, SecIsMul D.toPre.P.A.hom ϖ g g' := by
  obtain ⟨n, a₀, τ, τF, hτ, hva, hsum⟩ := h
  have hb : ∀ i, 0 < v (a₀ i) := fun i => by
    refine lt_of_lt_of_le ?_ (hva i)
    exact_mod_cast hr
  have vc : ∀ (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))) (x : F)
      {Z : Scheme.{0}} (q : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (j),
      q z ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j →
      gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (DegPre.constBF D.toPre F x _ * t.f j) =
        cst (q ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z x *
          gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (t.f j) := fun t x Z q z j hz =>
    (gs_mul q z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res q z le_top hz _).trans
      (gs_pull q (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _)) rfl)
  have div₁ := H1.dvd_of_comb hϖ D.toPre F v hv g τ a₀ hb (fun Z q z J hJ =>
    (H1.sval_scal hg q z hJ).symm.trans
      ((congrArg (gs _ z _) (hsum _)).trans ((H1.gs_sum q z _ (hJ.mem _ q) _).trans (Finset.sum_congr rfl fun i _ =>
        (vc (τF i) (a₀ i) q z _ (hJ.mem _ q)).trans (congrArg₂ (· * ·) rfl (H1.sval_scal (hτ i) q z hJ))))))
  have := D.toPre.P.isAb.smooth
  exact exists_div_sec D.toPre.P.A.hom hϖ.ne_zero g div₁

theorem isUnit_of_generates {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
    {k : ℕ} {α : D.toPre.X} {s t : D.toPre.SecB k α} (hs : SecBGenerates k α s) {a : R}
    (h : SecIsMul D.toPre.P.A.hom a s t) : IsUnit a := by
  obtain ⟨b, hb, -⟩ := hs t
  have h₁ : SecIsMul D.toPre.P.A.hom 1 s s := fun j => by simp only [scal, resTop, map_one, _root_.one_mul]
  have h₂ : SecIsMul D.toPre.P.A.hom (a * b) s s := fun j => by
    conv_lhs => rw [h j, hb j]
    simp only [scal, resTop, map_mul, _root_.mul_assoc]
  exact IsUnit.of_mul_eq_one b ((hs s).unique h₂ h₁)

theorem main : Laws → ThetaSectionValuationZero := by
  intro _ V _ _ _ ϖ hϖ D Q hQ vK hv A G _ _ U ϑ hϑ s hs E hE
  obtain ⟨g, hgE, hg⟩ := GlobalTheory.T.expansion_of_integral_section_is_integral V ϖ hϖ D A G U.toUnifPre 1 ϑ s hs E hE
  refine ⟨(GlobalTheory.integralFamily_levelOne V ϖ hϖ D Q hQ _ vK hv E g hg).1, ?_⟩
  rintro ⟨r, hr, hν⟩
  have h0 := hν 0
  rw [QForm.Q_zero hϖ D hQ, Int.cast_zero, zero_div, add_zero] at h0
  obtain ⟨g', hg'⟩ := dvd_of_vGe hϖ D _ vK hv 1 0 (E.s 0) (g 0) (hg 0) hr h0
  obtain ⟨f, hfE, hf⟩ := hϑ 0
  have hd := GlobalTheory.expandsAt_sub V _ D A G U.toUnifPre 0 1 ϑ ϑ SecOps.secZero f g
    (fun α => SecOps.secAdd (f α) (SecOps.secNeg (g α))) (fun j => (sub_self _).symm)
    (fun α j => (sub_eq_add_neg _ _).symm) hfE (hgE 0)
  obtain ⟨h, hh⟩ := (GlobalTheory.ExtDiv.main V ϖ hϖ D A G U.toUnifPre 0 1 0 _).1
    (WeightPf.weightIndep V _ D A G U.toUnifPre 0 1 _ _ (fun j => map_zero _) hd 0)
  rw [zero_add, pow_one] at hh
  refine hϖ.not_isUnit (isUnit_of_generates (t := SecOps.secAdd h g') hf fun j => ?_)
  have e₁ : (f 0).f j + - (g 0).f j = _ := hh j
  have e₂ := hg' j
  show _ = _ * (h.f j + g'.f j)
  rw [mul_add, ← e₁, ← e₂, neg_add_cancel_right]

end GlobalTheory.ThetaNu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoCubePow
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowAdj

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]

theorem psum_comp_hom (q : G' ⟶ G) [IsMonHom q] {T' T : Over S} {n : ℕ} (x : Fin n → (T' ⟶ G'))
    (y : Fin n → (T ⟶ G)) (h : T' ⟶ T) (e : ∀ k, x k ≫ q = h ≫ y k) (I : Finset (Fin n)) :
    psum G' x I ≫ q = h ≫ psum G y I :=
  (Geo.Tor.psum_hom (MonoidHom.mk' (· ≫ q) fun a b => MonObj.mul_comp a b q) x I).trans
    ((congrArg (fun z => psum G z I) (funext e)).trans (Geo.Tor.psum_hom (Geo.Tor.preHom h) y I).symm)

theorem cls_cube_box {j : ℕ} (p : IsPowGrp G' G j) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hb : Geo.Tor.LBIso L' (boxLB L p.pr)) {T' T : Over S} {n : ℕ} (x : Fin n → (T' ⟶ G'))
    (y : Fin n → (T ⟶ G)) (h : Fin j → (T' ⟶ T)) (e : ∀ i k, x k ≫ p.pr i = h i ≫ y k)
    (h₁ : (cubeLB G' x L').IsLB) (h₂ : (cubeLB G y L).IsLB) :
    cls _ h₁ = ∑ i, pull (h i).left (cls _ h₂) := by
  have a := cls_linComb hL' _ _ h₁
  have b := cls_linComb hL _ _ h₂
  have c : cls L' hL' = ∑ i, pull (p.pr i).left (cls L hL) := by
    rw [(cls_eq_iff hL' (LB.isLB_linComb hL _ _)).2 hb, cls_linComb hL]
    simp only [one_smul]
  refine a.trans (Eq.trans ?_ (Finset.sum_congr rfl fun i _ => congrArg (pull (h i).left) b.symm))
  simp only [c, map_sum, map_zsmul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun I _ => ?_
  have := p.hom i
  rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, psum_comp_hom (p.pr i) x y (h i) (e i)]

theorem lbIso_cube_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (boxLB L p.pr) → ∀ (f g : G ⟶ G) (f' g' : G' ⟶ G'), (∀ i, f' ≫ p.pr i = p.pr i ≫ f) → (∀ i, g' ≫ p.pr i = p.pr i ≫ g) → Geo.Tor.LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) → Geo.Tor.LBIso (cubeLB G' ![fst G' G' ≫ f', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ g'] L') := by
  intro S G' G _ _ _ _ j p L L' hL hL' hb f g f' g' hf hg H
  have i₁ : (cubeLB G ![fst G G ≫ f, snd G G] L).IsLB := LB.isLB_linComb hL _ _
  have i₂ : (cubeLB G ![fst G G, snd G G ≫ g] L).IsLB := LB.isLB_linComb hL _ _
  have i₃ : (cubeLB G' ![fst G' G' ≫ f', snd G' G'] L').IsLB := LB.isLB_linComb hL' _ _
  have i₄ : (cubeLB G' ![fst G' G', snd G' G' ≫ g'] L').IsLB := LB.isLB_linComb hL' _ _
  refine (cls_eq_iff i₃ i₄).1 ?_
  rw [cls_cube_box p hL hL' hb _ _ (fun i => p.pr i ⊗ₘ p.pr i) (fun i k => by fin_cases k <;> simp [hf]) i₃ i₁,
    cls_cube_box p hL hL' hb _ _ (fun i => p.pr i ⊗ₘ p.pr i) (fun i k => by fin_cases k <;> simp [hg]) i₄ i₂,
    (cls_eq_iff i₁ i₂).2 H]

end GlobalTheory.PowAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedCrossIdentityGenericFibreStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.mixed_cross_identity_genericFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k₁ : ℕ) (s₁ : P.U.SecK k₁) (F₁ : Fam P.D.toPre (FractionRing V) k₁) (u₁ : P.U.SecK (k₁ * N)) (F₁' : Fam P.D.toPre (FractionRing V) (k₁ * N)), P.U.Expands k₁ s₁ F₁ → P.U.Expands (k₁ * N) u₁ F₁' → PullAl P.D (FractionRing V) P.oD a k₁ N F₁ F₁' → ∀ (k₂ : ℕ) (s₂ : P.U.SecK k₂) (F₂ : Fam P.D.toPre (FractionRing V) k₂) (u₂ : P.U.SecK (k₂ * N)) (F₂' : Fam P.D.toPre (FractionRing V) (k₂ * N)), P.U.Expands k₂ s₂ F₂ → P.U.Expands (k₂ * N) u₂ F₂' → PullAl P.D (FractionRing V) P.oD a k₂ N F₂ F₂' → ∀ m₁ m₂ : ℕ, m₁ * k₁ = m₂ * k₂ → ∀ (y : (pullback t.G.hom (jK V) : Scheme.{0})) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u₁ (𝟙 _) y J ^ m₁ * Geo.Tor.sval s₂ (endK (t.act.act a)) y J ^ m₂ = Geo.Tor.sval u₂ (𝟙 _) y J ^ m₂ * Geo.Tor.sval s₁ (endK (t.act.act a)) y J ^ m₁ := by
  first | exact @GlobalTheory.GenericCross.main | exact GlobalTheory.GenericCross.main | (intros; apply GlobalTheory.GenericCross.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SectionsPowerTwistBasisStableBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.sections_powerTwist_basis_stable_baseChange : (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M)) → (∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), 1 ≤ n → FirstCohomologyVanishes (pw P.L n)) → (∀ (X X' : Scheme.{0}) (e : X' ⟶ X) (M : LB X) (M' : LB X'), IsIso e → M.IsLB → M'.IsLB → (∃ w : LB.Iso M' (M.pull e), w.IsGen) → FirstCohomologyVanishes M → FirstCohomologyVanishes M') → (∀ (R K : Type) [CommRing R] [Field K] (g₀ : R →+* K) (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R), D₁ * D₀ = 0 → (∀ w : Fin b → K, (D₁.map g₀).mulVec w = 0 → ∃ v, (D₀.map g₀).mulVec v = w) → ∃ (r : R) (n : ℕ) (B : Matrix (Fin a) (Fin n) R), g₀ r ≠ 0 ∧ D₀ * B = 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g r) → ∀ v : Fin a → R', (D₀.map g).mulVec v = 0 → ∃! z : Fin n → R', (B.map g).mulVec z = v) → PolBaseChangeSt → (∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 1 ≤ n → Module.finrank Γ((Over.mk t).left, ⊤) (SecM P.A P.L n (Over.mk t)) = n ^ P.g) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (q : ℕ), 1 ≤ q → ∀ c : Over.mk t ⟶ P.A, ∃ d : Over.mk t ⟶ P.A, d ^ q = c ∧ ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3) ![(snd (Over.mk t) P.A).left, (translPt P.A c).left, (translPt P.A d).left] ![(q : ℤ) - 1, 1, -(q : ℤ)]), w.IsGen) → DVR.TwistBaseChangeStatement := by
  first | exact @GlobalTheory.TwistBC.main | exact GlobalTheory.TwistBC.main | (intros; apply GlobalTheory.TwistBC.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSectionGenericFibreStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.value_at_unitSection_genericFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k : ℕ) (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (u : P.U.SecK (k * N)) (F' : Fam P.D.toPre (FractionRing V) (k * N)), P.U.Expands k s F → P.U.Expands (k * N) u F' → PullAl P.D (FractionRing V) P.oD a k N F F' → ∀ (y : Spec (CommRingCat.of (FractionRing V))) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u unitK y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))).val * Geo.Tor.sval s unitK y J := by
  first | exact @GlobalTheory.GenericUnitValue.value_at_generic_unit | exact GlobalTheory.GenericUnitValue.value_at_generic_unit | (intros; apply GlobalTheory.GenericUnitValue.value_at_generic_unit <;> assumption)
end

