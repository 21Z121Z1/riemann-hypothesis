import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOf
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.ThetaOfArc

open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam GlobalTheory.IndivisibleSection GlobalTheory.ThetaUnit IsLocalRing

section General

variable {X : Scheme.{0}} {L : LB X}

theorem sectionOfLineBundleOne_iff_germs_eq {σ : H0 L 1} {θ : L.Sec} : SectionOfLineBundleOne σ θ ↔ ∀ (y : X) (k : L.ι), y ∈ L.U k →
    gs (𝟙 X) y (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k)) (σ.f fun _ => k) = gs (𝟙 X) y (L.U k) (θ.f k) := by
  refine ⟨fun h y k hy => ?_, fun h j hj => ?_⟩
  · rw [h (fun _ => k) (fun z hz => Set.mem_iInter.1 hz 0)]
    exact gs_res (𝟙 X) y _ (mem_chart_one (𝟙 X) y hy) _
  · obtain ⟨k, rfl⟩ : ∃ k', j = fun _ => k' := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
    exact fn_ext fun y hy => (h y k (hj hy)).trans (gs_res (𝟙 X) y hj hy _).symm

theorem exists_h0Sec_left (θ : L.Sec) : ∃ σ : H0 L 1, SectionOfLineBundleOne σ θ := by
  obtain ⟨t, ht⟩ := exists_powerSection_of_chartFunctions θ
  exact ⟨t, sectionOfLineBundleOne_iff_germs_eq.2 fun y k hy => ht _ (𝟙 X) y k hy⟩

theorem exists_h0Sec_right (σ : H0 L 1) : ∃ θ : L.Sec, SectionOfLineBundleOne σ θ := by
  have le : ∀ k : L.ι, L.U k ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) :=
    fun k y hy => mem_chart_one (𝟙 X) y hy
  refine ⟨⟨fun k => resG X (le k) (σ.f fun _ => k), fun i j => fn_ext fun y hy => ?_⟩,
    sectionOfLineBundleOne_iff_germs_eq.2 fun y k hy => (gs_res (𝟙 X) y (le k) hy _).symm⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.1 _)).trans
    ((gs_compat σ (𝟙 X) y (le i hy.1) (le j hy.2)).trans (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (Eq.symm ?_)))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.2 _))))))
  refine (gm_linComb L _ _ (𝟙 X) y _ _ (le i hy.1) (le j hy.2)).trans ?_
  simp

def Same {L' : LB X} (σ : H0 L 1) (θ : L'.Sec) : Prop := ∃ θ' : L.Sec, SectionOfLineBundleOne σ θ' ∧ HEq θ θ'

variable {L' : LB X}

theorem exists_same_left (h : L = L') (θ : L'.Sec) : ∃ σ : H0 L 1, Same σ θ := by
  subst h
  obtain ⟨σ, hσ⟩ := exists_h0Sec_left θ
  exact ⟨σ, θ, hσ, HEq.rfl⟩

theorem exists_same_right (h : L = L') (σ : H0 L 1) : ∃ θ : L'.Sec, Same σ θ := by
  subst h
  obtain ⟨θ, hθ⟩ := exists_h0Sec_right σ
  exact ⟨θ, θ, hθ, HEq.rfl⟩

theorem Same.unique (h : L = L') {σ : H0 L 1} {θ₁ θ₂ : L'.Sec} (h₁ : Same σ θ₁) (h₂ : Same σ θ₂) : θ₁ = θ₂ := by
  subst h
  obtain ⟨_, a₁, ⟨⟩⟩ := h₁
  obtain ⟨_, a₂, ⟨⟩⟩ := h₂
  have e : θ₁.f = θ₂.f := funext fun k => fn_ext fun y hy =>
    (sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hy).symm.trans (sectionOfLineBundleOne_iff_germs_eq.1 a₂ y k hy)
  cases θ₁
  cases θ₂
  cases e
  rfl

theorem Same.mul_iff (h : L = L') {R : Type} [CommRing R] (p : X ⟶ Sp R) (r : R) {σ σ' : H0 L 1} {θ θ' : L'.Sec}
    (h₁ : Same σ θ) (h₂ : Same σ' θ') : SecIsMul p r σ' σ ↔ ∀ i, θ'.f i = constFn p _ r * θ.f i := by
  subst h
  obtain ⟨_, a₁, ⟨⟩⟩ := h₁
  obtain ⟨_, a₂, ⟨⟩⟩ := h₂
  refine ⟨fun hm k => fn_ext fun y hy => ?_, fun hm j => ?_⟩
  · refine (sectionOfLineBundleOne_iff_germs_eq.1 a₂ y k hy).symm.trans
      ((secIsMul_gs hm (𝟙 X) y (fun _ => k) (mem_chart_one (𝟙 X) y hy)).trans (Eq.symm ?_))
    exact (gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_constFn p _ (𝟙 X) y hy r) (sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hy).symm)
  · obtain ⟨k, rfl⟩ : ∃ k', j = fun _ => k' := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
    rw [ThickDiv.resTop_scal]
    refine fn_ext fun y hy => ?_
    have hk : y ∈ L.U k := Set.mem_iInter.1 hy 0
    refine (sectionOfLineBundleOne_iff_germs_eq.1 a₂ y k hk).trans ((congrArg _ (hm k)).trans ((gs_mul (𝟙 X) y _ hk _ _).trans
      (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·) ?_ (sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hk))))))
    exact (gs_constFn p _ (𝟙 X) y hy r).trans (gs_constFn p _ (𝟙 X) y hk r).symm

theorem Same.mem_nonzeroLocus (h : L = L') {σ : H0 L 1} {θ : L'.Sec} (h₁ : Same σ θ) {y : X}
    (hy : y ∈ nonzeroLocus σ) : y ∈ nonzeroLocus θ := by
  subst h
  obtain ⟨_, a₁, ⟨⟩⟩ := h₁
  obtain ⟨j, hj, hu⟩ := (SectionBaseChange.mem_nonzeroLocus σ _).1 hy
  obtain ⟨k, rfl⟩ : ∃ k', j = fun _ => k' := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  have hk : y ∈ L.U k := Set.mem_iInter.1 hj 0
  exact (SectionBaseChange.mem_nonzeroLocus θ _).2 ⟨k, hk, sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hk ▸ hu⟩

end General

theorem isPullTerm_mul {R A : Type} [CommRing R] [IsDomain R] [CommRing A] {D : DegPre R} {B₀ : Scheme.{0}}
    {M₀ : LB B₀} {φ : D.P.A.left ⟶ B₀} {w : LB.Iso D.P.L (M₀.pull φ)} {th th' : M₀.Sec} (q : B₀ ⟶ Sp A)
    (f : A →+* R) (hq : φ ≫ q = D.P.A.hom ≫ spMap f) (r : A) (hm : ∀ j, th'.f j = constFn q _ r * th.f j)
    {t t' : D.SecB 1 0} (h : IsPullTerm D φ w th t) (ht : SecIsMul D.P.A.hom (f r) t' t) :
    IsPullTerm D φ w th' t' := by
  refine isPullTerm_iff.2 fun y J j₀ hJ hy => ?_
  rw [hm, gs_mul φ y _ hy, gs_constFn q _ φ y hy, isPullTerm_iff.1 h y J j₀ hJ hy, sval_of_secIsMul ht _ y hJ, hq,
    cst_comp, Category.id_comp, mul_left_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X}

theorem thetaOf_iff (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (θ : LB.Sec W.t.PP.L) : ThetaOf W th θ ↔
    ∃ (σ : H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x), (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 σ fam) ∧
      IsPullTerm W.P.D.toPre W.φ W.w th (fam 0) ∧ Same σ θ :=
  ⟨fun ⟨σ, fam, θ', h₁, h₂, h₃⟩ => ⟨σ, fam, h₁, h₂, θ', h₃⟩, fun ⟨σ, fam, h₁, h₂, θ', h₃⟩ => ⟨σ, fam, θ', h₁, h₂, h₃⟩⟩

theorem secIsMul_of_weight_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {P : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D P G)
    (σ σ' : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))))
    (f f' : ∀ α, SecBMod D.toPre 1 α) (hE : ∀ e, U.ExpandsAt e 1 σ f) (hE' : ∀ e, U.ExpandsAt e 1 σ' f')
    (hu : ∀ (σ₁ : H0 U.LG.L 1) (f₁ : ∀ α, D.toPre.SecB 1 α), f₁ 0 = f 0 → (∀ e, U.ExpandsAt e 1 σ₁ f₁) → σ₁ = σ)
    (r : R) (h : SecIsMul D.toPre.P.A.hom r (f' 0) (f 0)) : SecIsMul G.hom r σ' σ := by
  have h₀ : f' 0 = r • f 0 := (secIsMul_iff _ _ _ _).1 h
  have h₁ : (f' + (1 - r) • f) 0 = f 0 := by
    rw [Pi.add_apply, Pi.smul_apply, h₀, ← add_smul, add_sub_cancel, one_smul]
  have h₂ : σ' + (1 - r) • σ = σ :=
    hu _ _ h₁ fun e => expandsAt_add U (hE' e) (expandsAt_smul U (1 - r) (hE e))
  refine (secIsMul_iff _ _ _ _).2 ?_
  rw [sub_smul, one_smul] at h₂
  rw [← sub_eq_zero, ← add_left_inj σ, zero_add]
  refine Eq.trans ?_ h₂
  abel

end GlobalTheory.ThetaOfArc

namespace GlobalTheory

open GlobalTheory.ThetaUnit GlobalTheory.ThetaOfArc IsLocalRing

theorem existsUnique_thetaOf : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec), ThNZ th → (∃! θ : LB.Sec W.t.PP.L, ThetaOf W th θ) ∧ ∀ θ, ThetaOf W th θ → (∀ s : LB.Sec W.t.PP.L, ∃! r : PowerSeries A, ∀ i, s.f i = constFn W.t.G.hom _ r * θ.f i) ∧ (∃ g : W.t.G.left, W.t.G.hom g = IsLocalRing.closedPoint (PowerSeries A) ∧ g ∈ Out.nonzeroLocus θ) ∧ ∀ (r : A) (th' : a.D₀.P.L.Sec) (θ' : LB.Sec W.t.PP.L), ThMul r th th' → (ThetaOf W th' θ' ↔ ∀ i, θ'.f i = constFn W.t.G.hom _ (PowerSeries.C (R := A) r) * θ.f i) := by
  intro hL _ E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W th hth
  have hI : Ideal.span {(PowerSeries.X : PowerSeries A)} ≤ maximalIdeal (PowerSeries A) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have hb : W.P.U.LG.L = W.t.PP.L := congrArg (fun q => q.L) W.P.bundle
  obtain ⟨⟨t, ht, htu⟩, hnz⟩ := existsUnique_pullTerm W th
  have ht₀ := hnz t ht hth (closedPoint _)
  obtain ⟨σ, fam, rfl, hE, hmem, huq, hgen, -⟩ := exists_theta_arc hL.globalFns hL.secBaseChange hI W t ht₀
  have key : ∀ θ, ThetaOf W th θ ↔ Same σ θ := fun θ => by
    rw [thetaOf_iff]
    refine ⟨fun ⟨σ₁, f₁, h₁, h₂, h₃⟩ => huq σ₁ f₁ (htu _ h₂) h₁ ▸ h₃, fun h => ⟨σ, fam, hE, ht, h⟩⟩
  refine ⟨?_, fun θ hθ => ⟨fun s => ?_, ?_, fun r th' θ' hm => ?_⟩⟩
  · obtain ⟨θ, hθ⟩ := exists_same_right hb σ
    exact ⟨θ, (key θ).2 hθ, fun θ' h => ((key θ').1 h).unique hb hθ⟩
  · obtain ⟨s', hs'⟩ := exists_same_left hb s
    simpa only [((key θ).1 hθ).mul_iff hb W.t.G.hom _ hs'] using hgen s'
  · obtain ⟨g, hg, hn⟩ := exists_mem_nonzeroLocus hI W.P.U.toUnifPre (hE 0) ht₀ hmem
    exact ⟨g, hg, ((key θ).1 hθ).mem_nonzeroLocus hb hn⟩
  · choose fam' hfam' using fun α =>
      IntegralExpansion.exists_secIsMul W.P.D.toPre.P.A.hom (PowerSeries.C (R := A) r) (fam α)
    have hp : IsPullTerm W.P.D.toPre W.φ W.w th' (fam' 0) :=
      isPullTerm_mul a.D₀.P.A.hom _ W.spec.1.1.w r hm ht (hfam' 0)
    rw [thetaOf_iff]
    refine ⟨fun ⟨σ₁, f₁, h₁, h₂, h₃⟩ => (((key θ).1 hθ).mul_iff hb W.t.G.hom _ h₃).1 ?_, fun h => ?_⟩
    · exact secIsMul_of_weight_zero W.P.U.toUnifPre σ σ₁ fam f₁ hE h₁ huq _
        (h₂.unique a.D₀.P.isLB hp ▸ hfam' 0)
    · obtain ⟨σ', hσ'⟩ := exists_same_left hb θ'
      exact ⟨σ', fam', fun n => expandsAt_secIsMul _ _ _ _ _ _ n 1 _ σ σ' fam fam'
        ((((key θ).1 hθ).mul_iff hb W.t.G.hom _ hσ').2 h) hfam' (hE n), hp, hσ'⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FirstOrderJetConstSectionMulCoordinate
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanJet

open FrameValue

theorem jet_comp_equiv {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    (e : V' ≃L[ℂ] V) (F : V → ℂ) (z : V') : jet (fun w => F (e w)) z = jet F (e z) := by
  have h := e.comp_right_fderiv (f := F) (x := 0)
  rw [map_zero] at h
  ext
  · simp
  · rw [snd_jet, snd_jet]
    exact congrArg (fun q : V' →L[ℂ] ℂ => q z) h

theorem valR_eq_jet {g : ℕ} {X : Scheme.{0}} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {z : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hd : IsDerivAt0 e z v) (U : X.Opens) (hU : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR v U f = jet (fun w => valAt' (e w) U f) z := by
  ext
  · rw [fst_jet, ← hd.1]
    exact (FormalValue.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom v U hU f).symm
  · rw [snd_jet, ← hd.2 U hU f, valR, dif_pos hU]

theorem frameProd_mul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {n : ℕ} (u : HolUnif A L n) (j : ℕ)
    (c z : Fin n → ℂ) (k : Fin 4 → L.ι) (hk : ∀ i, ⊤ ≤ (u.ex (![c + z, c, z, 0] i)).left ⁻¹ᵁ L.U (k i)) :
    frameProd u (Out.DegPre.famε j) ![z, z + c, c, 0] ![k 2, k 0, k 1, k 3] *
      frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k = u.fr (k 2) z ^ j := by
  have n₀ : u.fr (k 0) (c + z) ≠ 0 := u.fr_ne _ _ (hk 0)
  have n₁ : u.fr (k 1) c ≠ 0 := u.fr_ne _ _ (hk 1)
  have n₂ : u.fr (k 2) z ≠ 0 := u.fr_ne _ _ (hk 2)
  have n₃ : u.fr (k 3) 0 ≠ 0 := u.fr_ne _ _ (hk 3)
  simp only [frameProd, Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub₀ n₂,
    zpow_neg, zpow_one, zpow_natCast, add_comm z c]
  field_simp

theorem jet_sec_mul_coord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (j : ℕ) (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (jt₀ : Fin 4 → a.D₀.P.L.ι), IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (h.symm z)).b.left)) z₀ ν.b.left → (∀ x j, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j → valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val = TrivSqZeroExt.inl (chiVal (Λ.ex0 (h.symm 0)) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (Λ.ex0 (h.symm z)) x j) 0 z₀)) → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀ → valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀) ((ν.s (Λ.ε α)).s jt₀).val = jet (fun v : Λ.A.V => Λ.fn j α s₀ v.2 * eTwoPi (v.1 α)) (h.symm z₀) * jet (fun v : Λ.A.V => Λ.u.fr (jt₀ 2) v.2) (h.symm z₀) ^ j := by
  intro E _ _ _ H _ D l c O _ β _ _ b a Λ g h z₀ ν j α s₀ jt hd hs hj
  have hU : ⊤ ≤ (show Sp (DualNumber ℂ) ⟶ _ from ν.b.left) ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] := by
    intro y hy
    refine Set.mem_iInter.2 fun i => ?_
    have h₁ := Set.mem_iInter.1 (hj hy) (![2, 0, 1, 3] i)
    have h₂ : (![jt 2, jt 0, jt 1, jt 3] : Fin 4 → _) i = jt (![2, 0, 1, 3] i) := by fin_cases i <;> rfl
    rw [h₂]
    exact (congrArg (fun q => q y ∈ a.D₀.P.L.U (jt (![2, 0, 1, 3] i)))
      (ConstTerm.comp_famφB a.D₀ ν.b (Λ.ε α) i)).mpr h₁
  have h0 : ⊤ ≤ (Λ.u.ex (0 : Λ.A.V).2).left ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] := by
    have h₁ := FormalValue.top_le_comp hU (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    have h₂ := hd.1.trans (Λ.ex0_b (h.symm 0))
    rw [map_zero] at h₂
    exact h₂ ▸ h₁
  obtain ⟨ho, hh⟩ := Λ.u.hol _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])
  have hn : ∀ᶠ v : Λ.A.V in nhds 0, ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] :=
    (ho.preimage continuous_snd).mem_nhds h0
  have lf := ConstTerm.isLift_famφB Λ.u (Λ.ct α)
  have hk : ∀ z, ⊤ ≤ (Λ.u.ex z).left ⁻¹ᵁ LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] →
      ∀ i, ⊤ ≤ (Λ.u.ex (![Λ.A.ct α + z, Λ.A.ct α, z, 0] i)).left ⁻¹ᵁ a.D₀.P.L.U (jt i) := fun z hz i => by
    have h₁ := ((lf z).le_iff _).1 hz
    fin_cases i
    exacts [add_comm z (Λ.A.ct α) ▸ h₁ 1, h₁ 2, h₁ 0, h₁ 3]
  have hg : ∀ᶠ v : Λ.A.V in nhds 0, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 v).b (Λ.ε α)) jt :=
    hn.mono fun v hv => ((gtHol_isLift a.D₀ Λ.u _ _ _ _ (Λ.ct α) (Λ.ex0_b v)).le_iff jt).2 (hk _ hv)
  obtain ⟨hc₁, hc₂⟩ := (analyticDictionaryExp_holomorphic_over_unif E H D l c O β b a Λ).2 (Λ.ε α) jt
  simp only [LinearEquiv.symm_apply_apply] at hc₂
  have dF : DifferentiableAt ℂ (fun v : Λ.A.V => valAt' (Λ.u.ex v.2).left _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])) 0 :=
    (hh.differentiableAt (ho.mem_nhds h0)).comp (0 : Λ.A.V) differentiableAt_snd
  have dG : DifferentiableAt ℂ (fun v : Λ.A.V => chiVal (Λ.ex0 v) (Λ.ε α) jt) 0 := hc₁.differentiableAt hg
  have dfn : Differentiable ℂ (Λ.fn j α s₀) := by
    have := differentiable_secVal a.D₀.P.isLB s₀ (𝟙 _) (q := id) differentiable_id
      (z := fun z => ![z, z + Λ.A.ct α, Λ.A.ct α, 0])
      (fun k => by fin_cases k <;> simp <;> fun_prop) (fun w => by rw [id, Category.comp_id]; exact lf w)
    simp only [id, Category.comp_id] at this
    exact this
  have dP : DifferentiableAt ℂ (fun v : Λ.A.V => Λ.fn j α s₀ v.2 * eTwoPi (v.1 α)) 0 := by
    have : Differentiable ℂ (fun z : Λ.A.V => z.1 α) := (Λ.A.evalCLM α).differentiable.comp differentiable_fst
    exact ((dfn.comp differentiable_snd).fun_mul (this.const_mul _).cexp) 0
  have dQ : DifferentiableAt ℂ (fun v : Λ.A.V => Λ.u.fr (jt 2) v.2) 0 :=
    ((Λ.u.fr_hol (jt 2)).differentiableAt ((Λ.u.hol _ 0).1.mem_nhds (hk _ h0 2))).comp (0 : Λ.A.V)
      differentiableAt_snd
  have e₁ := valR_eq_jet hd _ hU (s₀.f ![jt 2, jt 0, jt 1, jt 3])
  simp only [Λ.ex0_b] at e₁
  replace e₁ := e₁.trans (jet_comp_equiv h.symm
    (fun v : Λ.A.V => valAt' (Λ.u.ex v.2).left _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])) z₀)
  have e₂ := (hs (Λ.ε α) jt hj).trans (jet_comp_equiv h.symm (fun v : Λ.A.V => chiVal (Λ.ex0 v) (Λ.ε α) jt) z₀)
  refine (congrArg₂ (· * ·) e₁ e₂).trans ?_
  rw [← jet_mul dF dG, ← jet_pow dQ, ← jet_mul dP (dQ.fun_pow j)]
  refine jet_congr ?_ _
  filter_upwards [hn, hg] with v hv hv'
  refine (congrArg₂ (· * ·) (valAt'_sec a.D₀.P.isLB s₀ (lf v.2) hv) (hc₂ v hv')).trans ?_
  rw [← frameProd_mul Λ.u j (Λ.A.ct α) v.2 jt (hk _ hv), _root_.mul_mul_mul_comm]
  rfl

end GlobalTheory.ConstTanJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTangentGenericFibreOfThetaSections
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.GenericTan

section Charts

variable {R : Type} [CommRing R] [IsLocalRing R] {Z Z' : Scheme.{0}} {L : LB Z}

theorem valR_cocycle (hL : L.IsLB) (x : Sp R ⟶ Z) {i j k : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valR x (L.U i ⊓ L.U j) (L.g i j).val * valR x (L.U j ⊓ L.U k) (L.g j k).val =
      valR x (L.U i ⊓ L.U k) (L.g i k).val := by
  apply toStkA_injective
  rw [map_mul, toStkA_valR x (L.U i ⊓ L.U j) _ (fun _ hz => ⟨hi hz, hj hz⟩),
    toStkA_valR x (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩),
    toStkA_valR x (L.U i ⊓ L.U k) _ (fun _ hz => ⟨hi hz, hk hz⟩), ← Units.val_mul,
    gm_cocycle hL x _ (hi trivial) (hj trivial) (hk trivial)]

theorem valR_self (hL : L.IsLB) (x : Sp R ⟶ Z) {j : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  apply toStkA_injective
  rw [toStkA_valR x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨h hz, h hz⟩), map_one]
  exact congrArg Units.val (gm_self hL x _ (h trivial))

theorem isFrm_spread (hL : L.IsLB) (x : Sp R ⟶ Z) {k : L.ι} (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) {a : R} (ha : IsUnit a) :
    IsFrm L x (fun j => valR x (L.U j ⊓ L.U k) (L.g j k).val * a) := by
  refine ⟨fun j hj => (FormalValue.isUnit_valR x (L.U j ⊓ L.U k) (fun _ hz => ⟨hj hz, hk hz⟩) _).mul ha,
    fun j j' h => ?_⟩
  rw [← _root_.mul_assoc, valR_cocycle hL x (fun _ hz => (h hz).1) (fun _ hz => (h hz).2) hk]

theorem sval_chart {p : Z' ⟶ Z} {m : ℕ} (s : SecP L p m) (q : Sp R ⟶ Z') {j k : L.ι}
    (hj : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U j) (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) :
    ArcPts.sval s q j = valR (q ≫ p) (L.U j ⊓ L.U k) (L.g j k).val ^ m * ArcPts.sval s q k := by
  have wj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) :=
    fun z hz => Set.mem_iInter.2 fun _ => hj hz
  have wk : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => k) :=
    fun z hz => Set.mem_iInter.2 fun _ => hk hz
  apply toStkA_injective
  rw [map_mul, map_pow, toStkA_valR (q ≫ p) (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩)]
  refine (FormalValue.toStkA_valR_eq_gs q _ _ wj _).trans ((sec_trans s q _ (wj trivial) (wk trivial)).trans
    (congrArg₂ (· * ·) ?_ (FormalValue.toStkA_valR_eq_gs q _ _ wk _).symm))
  rw [trF, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]

theorem hasVal_of_chart {p : Z' ⟶ Z} {m : ℕ} (s : SecP L p m) (q : Sp R ⟶ Z') {τ : L.ι → R}
    (hτ : IsFrm L (q ≫ p) τ) {k : L.ι} (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) {r : R}
    (h : ArcPts.sval s q k = r * τ k ^ m) : HasVal s q τ r := fun j hj => by
  rw [sval_chart s q hj hk, h, hτ.2 j k (fun _ hz => ⟨hj hz, hk hz⟩), mul_pow, mul_left_comm]

def pullPow (p : Z' ⟶ Z) {m : ℕ} (σ : Out.H0 L m) : SecP L p m :=
  have l : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => p) j ≤ p ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 Z) j :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  { f := fun j => (p.appLE _ _ (l j)).hom (σ.f j)
    compat := fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => by
      have v : ∀ j : Fin 1 → L.ι, y ∈ LB.wchart L (fun _ : Fin 1 => p) j →
          gs (𝟙 Z') y _ ((p.appLE _ _ (l j)).hom (σ.f j)) =
          gs (𝟙 Z' ≫ p) y (LB.wchart L (fun _ : Fin 1 => 𝟙 Z) j) (σ.f j) := fun j hj =>
        (gs_res (𝟙 Z') y (l j) hj _).trans (gs_pull _ p y _ (l j hj) _)
      refine ((gs_res (𝟙 Z') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Z') y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Z') y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Z') y j j' hy.1 hy.2)))
          ((gs_res (𝟙 Z') y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans σ (𝟙 Z' ≫ p) y (l j hy.1) (l j' hy.2)]
      simp only [trF, Category.comp_id] }

omit [IsLocalRing R] in
theorem sval_pullPow (p : Z' ⟶ Z) {m : ℕ} (σ : Out.H0 L m) (q : Sp R ⟶ Z') {k : L.ι}
    (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) : ArcPts.sval (pullPow p σ) q k =
      valR (q ≫ p) (LB.wchart L (fun _ : Fin 1 => 𝟙 Z) (fun _ => k)) (σ.f (fun _ => k)) :=
  HolHom.valR_appLE q p _ _ _ _ (fun z hz => Set.mem_iInter.2 fun _ => hk hz)

omit [IsLocalRing R] in
theorem le_powChart {x : Sp R ⟶ Z} {k : L.ι} (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 Z) (fun _ => k) :=
  fun _ hz => Set.mem_iInter.2 fun _ => hk hz

end Charts

theorem isTan_of_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (A : AnArc (𝓞 E)) (t : SAB H (Sp ℂ⟦X⟧)) (Φ : GenPts A t gen) (L : RigLB t.G) (x : A.V → (Sp ℂ⟦X⟧ ⟶ t.G.left)) (τ : A.V → L.L.ι → ℂ⟦X⟧) (z : A.V) (v : Sp (DualNumber ℂ⟦X⟧) ⟶ t.G.left) (k₀ : L.L.ι) (τ₁ : DualNumber ℂ⟦X⟧) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom gen), L = t.PP → (∀ u, (Φ.x u).left = gen ≫ x u ∧ ∀ (k : L.L.ι) (k' : t.PP.L.ι), HEq k k' → ⊤ ≤ x u ⁻¹ᵁ L.L.U k → Φ.τ u k' = algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k)) → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v = x 0 → ⊤ ≤ v ⁻¹ᵁ L.L.U k₀ → IsUnit τ₁ → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → (∀ (j : ℕ) [NeZero j] (α : A.X), ∀ th ∈ A.Theta j α, ∀ F, IsDFSum A j α th z F → ∃ (m : ℕ) (σ : Out.H0 L.L j), (∀ u k, ⊤ ≤ x u ⁻¹ᵁ L.L.U k → algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (valR (x u) (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k)) (σ.f (fun _ => k))) = HahnSeries.single (m : ℤ) (1 : ℂ) * A.FSum j α th u * algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k) ^ j) ∧ ρ (valR v (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k₀)) (σ.f (fun _ => k₀))) = TrivSqZeroExt.inl (HahnSeries.single (m : ℤ) (1 : ℂ)) * (TrivSqZeroExt.inl (A.FSum j α th 0) + TrivSqZeroExt.inr F) * ρ τ₁ ^ j) → Φ.IsTan z νK := by
  intro E _ _ _ H _ A t Φ L x τ z v k₀ τ₁ ρ νK hL hx hv hk₀ hτ₁ hρ hε hfst hsnd hsec
  subst hL
  have hρ' := eq_dualMapR _ ρ hρ hε
  have hK : ⊤ ≤ (νK ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U k₀ := by
    rw [hfst]; exact FormalValue.top_le_comp hk₀ _
  haveI := isLocalRing_dual ℂ⸨X⸩
  have hfrm := isFrm_spread t.PP.isLB (νK ≫ pullback.fst _ _) hK (hτ₁.map ρ)
  refine ⟨hsnd, ?_, _, hfrm, fun j _ α th hth F hF => ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst, fib, pullback.lift_fst, (hx 0).1, ← hv, ← Category.assoc, ← Category.assoc,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext1
      refine RingHom.ext fun a => ?_
      rw [hρ']
      exact fst_dualMapR _ a
    · rw [Category.assoc, hsnd, fib, pullback.lift_snd, ← Spec.map_comp, ← Spec.map_id]
      congr 1
  · obtain ⟨m, σ, h₁, h₂⟩ := hsec j α th hth F hF
    have key := sval_eq_sum_of_hasVal E H _ A t gen Φ j (pullPow (pullback.fst t.G.hom gen) σ) 1
      (fun _ => HahnSeries.single (m : ℤ) (1 : ℂ)) (fun _ => α) (fun _ => th) (fun _ => hth) (fun u => by
        have e : fib (Φ.x u) ≫ pullback.fst t.G.hom gen = gen ≫ x u := by
          rw [fib, pullback.lift_fst, (hx u).1]
        obtain ⟨k, hk⟩ := exists_chart t.PP.isLB (x u (cpt ℂ⟦X⟧))
        have hk' := (top_le_iff_cpt _ _).2 hk
        have hk'' : ⊤ ≤ (fib (Φ.x u) ≫ pullback.fst t.G.hom gen) ⁻¹ᵁ t.PP.L.U k := by
          rw [e]; exact FormalValue.top_le_comp hk' _
        refine hasVal_of_chart _ _ ?_ hk'' ?_
        · rw [e, ← (hx u).1]; exact Φ.frm u
        · rw [sval_pullPow _ _ _ hk'', e, Fin.sum_univ_one, (hx u).2 k k HEq.rfl hk', ← h₁ u k hk']
          exact FormalValue.valR_spMap _ _ _ (le_powChart hk') _)
      _ _ νK hsnd k₀ hK
    refine hasVal_of_chart _ _ hfrm hK ?_
    rw [sval_pullPow _ _ _ hK, hfst, Fin.sum_univ_one, TrivSqZeroExt.algebraMap_eq_inl] at key
    replace key := (h₂.symm.trans (FormalValue.valR_spMap ρ v _ (le_powChart hk₀) _).symm).trans key
    rw [_root_.mul_assoc] at key
    have hu : IsUnit (TrivSqZeroExt.inl (HahnSeries.single (m : ℤ) (1 : ℂ)) : DualNumber ℂ⸨X⸩) :=
      TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit (by simp))
    rw [valR_self t.PP.isLB _ hK, _root_.one_mul]
    exact (hu.mul_left_cancel key).symm

end GlobalTheory.GenericTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionOfArcNonzeroOnFibres
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ThetaAllFibres

theorem exists_mem_of_flat {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    (U : X.Opens) {x : X} (hx : p x = IsLocalRing.closedPoint R) (hU : x ∈ U) (g : Sp R) :
    ∃ y : X, p y = g ∧ y ∈ U := by
  have hs : g ⤳ p x := hx ▸ IsLocalRing.specializes_closedPoint (R := R) g
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap p hs
  exact ⟨y, e, hy.mem_open U.isOpen hU⟩

theorem mem_nonzeroLocus_of_h0Sec {X : Scheme.{0}} {L : LB X} {σ : Out.H0 L 1} {θ : LB.Sec L} (h : SectionOfLineBundleOne σ θ) {x : X}
    (hx : x ∈ Out.nonzeroLocus σ) : x ∈ Out.nonzeroLocus θ := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have le : LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun y hy => Set.mem_iInter.1 hy 0
  rw [h j le] at hj
  erw [Scheme.basicOpen_res] at hj
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j 0, hj.2⟩

theorem nonzeroLocus_eq_of_heq {S : Scheme.{0}} {G : Over S} [GrpObj G] {L L' : RigLB G} (e : L' = L)
    {θ : LB.Sec L.L} {θ' : LB.Sec L'.L} (h : HEq θ θ') : Out.nonzeroLocus θ = Out.nonzeroLocus θ' := by
  subst e
  rw [eq_of_heq h]

theorem X_notMem_or_eq_closedPoint {A : Type} [CommRing A] [IsLocalRing A] (hA : IsField A)
    (g : PrimeSpectrum (PowerSeries A)) :
    PowerSeries.X ∉ g.asIdeal ∨ g = IsLocalRing.closedPoint (PowerSeries A) := by
  refine or_iff_not_imp_left.2 fun h => ?_
  rw [not_not] at h
  refine PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal g.isPrime.ne_top) fun f hf => ?_)
  have h₀ : PowerSeries.constantCoeff f = 0 := by
    by_contra hne
    obtain ⟨b, hb⟩ := hA.mul_inv_cancel hne
    exact (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal f).1 hf))
      (PowerSeries.isUnit_iff_constantCoeff.2 (IsUnit.of_mul_eq_one b hb))
  obtain ⟨q, rfl⟩ := PowerSeries.X_dvd_iff.2 h₀
  exact g.asIdeal.mul_mem_right _ h

theorem theta_nonzero_on_fibres : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (θ : LB.Sec W.t.PP.L), ThNZ th → ThetaOf W th θ → (IsField A ∨ PushInvertible Y.t.G Y.t.PP.L) → ∀ g : Sp (PowerSeries A), (IsField A → PowerSeries.X ∉ g.asIdeal ∨ g = IsLocalRing.closedPoint (PowerSeries A)) ∧ ∃ x : W.t.G.left, W.t.G.hom x = g ∧ x ∈ Out.nonzeroLocus θ := by
  intro hL _ E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W th θ hth hθ _ g
  refine ⟨fun hA => X_notMem_or_eq_closedPoint hA g, ?_⟩
  obtain ⟨σ, fam, θ', hE, hp, h0, he⟩ := hθ
  have hI : Ideal.span {(PowerSeries.X : PowerSeries A)} ≤ IsLocalRing.maximalIdeal (PowerSeries A) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have := W.t.semi.geomConnected
  have := W.P.U.smooth
  obtain ⟨σ₀, -, -, -, -, hu, -, hz⟩ := GlobalTheory.ThetaUnit.exists_theta hL.globalFns hL.secBaseChange hI W.P.U (fam 0)
    ((GlobalTheory.ThetaUnit.existsUnique_pullTerm W th).2 (fam 0) hp hth _)
  obtain rfl := hu σ fam rfl hE
  obtain ⟨x, hx, hn⟩ := (hz σ 1 ((GlobalTheory.ThetaUnit.secIsMul_iff _ _ _ _).2 (one_smul _ _).symm)).2.1 isUnit_one
  rw [nonzeroLocus_eq_of_heq W.P.bundle he]
  exact exists_mem_of_flat W.t.G.hom _ hx (mem_nonzeroLocus_of_h0Sec h0 hn) g

end GlobalTheory.ThetaAllFibres
end

