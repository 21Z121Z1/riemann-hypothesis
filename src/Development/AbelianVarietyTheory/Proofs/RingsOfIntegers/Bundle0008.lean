import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemBasicOpenIffGs
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.SectionRatio

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem mem_basicOpen_iff_gs {Y : Scheme.{0}} {U : Y.Opens} (f : Γ(Y, U)) (y : Y) (hy : y ∈ U) :
    y ∈ Y.basicOpen f ↔ IsUnit (gs (𝟙 Y) y U f) := by
  rw [gs_eq (𝟙 Y) y U hy f, Scheme.mem_basicOpen Y f y hy]
  exact Iff.rfl

theorem exists_quot {Y : Scheme.{0}} {U : Y.Opens} (a b : Γ(Y, U)) :
    ∃ q : Γ(Y, Y.basicOpen b), ∀ y ∈ Y.basicOpen b,
      gs (𝟙 Y) y _ q * gs (𝟙 Y) y U b = gs (𝟙 Y) y U a := by
  have hD : Y.basicOpen b ≤ U := Y.basicOpen_le b
  have hu : IsUnit ((Y.presheaf.map (homOfLE hD).op).hom b) := Y.toRingedSpace.isUnit_res_basicOpen b
  obtain ⟨w, hw⟩ := hu
  refine ⟨(Y.presheaf.map (homOfLE hD).op).hom a * ↑w⁻¹, fun y hy => ?_⟩
  have key : ((Y.presheaf.map (homOfLE hD).op).hom a * ↑w⁻¹) * (Y.presheaf.map (homOfLE hD).op).hom b =
      (Y.presheaf.map (homOfLE hD).op).hom a := by
    have hw' : (Y.presheaf.map (homOfLE hD).op).hom b = ↑w := hw.symm
    rw [hw', _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
  rw [← gs_res (𝟙 Y) y hD hy b, ← gs_mul (𝟙 Y) y _ hy, key, gs_res (𝟙 Y) y hD hy a]

private theorem exists_global_unit_of_compatible_of_iSup_eq {Y : Scheme.{0}} {P : Type} (W : P → Y.Opens) (hW : ∀ y, ∃ p, y ∈ W p)
    (q : ∀ p, Γ(Y, W p))
    (hq : ∀ p p' (y : Y), y ∈ W p → y ∈ W p' → gs (𝟙 Y) y (W p) (q p) = gs (𝟙 Y) y (W p') (q p')) :
    ∃ c : Γ(Y, ⊤), ∀ p (y : Y), y ∈ W p → gs (𝟙 Y) y ⊤ c = gs (𝟙 Y) y (W p) (q p) := by
  have hcov : (⊤ : Y.Opens) ≤ iSup W := fun y _ => by
    obtain ⟨p, hp⟩ := hW y
    exact Opens.mem_iSup.2 ⟨p, hp⟩
  have hcomp : TopCat.Presheaf.IsCompatible Y.sheaf.1 W q := by
    intro p p'
    apply fn_ext
    intro y hy
    exact (gs_res (𝟙 Y) y inf_le_left hy (q p)).trans
      ((hq p p' y hy.1 hy.2).trans (gs_res (𝟙 Y) y inf_le_right hy (q p')).symm)
  obtain ⟨c, hc, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf W ⊤ (fun p => homOfLE le_top) hcov q hcomp
  refine ⟨c, fun p y hy => ?_⟩
  rw [← hc p]
  exact (gs_res (𝟙 Y) y le_top hy c).symm

private theorem gs_id_linComb_eq_trF_mul_sval {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (j : K → L.ι) (y : Y) (hy : y ∈ (LB.LinComb L φ ε).U j)
    (J : (Y ⟶ X) → L.ι) (hJ : Good L y J) :
    gs (𝟙 Y) y ((LB.LinComb L φ ε).U j) (s.f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval s (𝟙 Y) y J :=
  sec_trans s (𝟙 Y) y hy (hJ.mem φ (𝟙 Y))

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {Ix : Type} (a b : Ix → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ (y : Y) (J), Good L y J → ∃ i, IsUnit (sval (b i) (𝟙 Y) y J))
    (hab : ∀ i i' (y : Y) (J), Good L y J →
      sval (a i) (𝟙 Y) y J * sval (b i') (𝟙 Y) y J = sval (a i') (𝟙 Y) y J * sval (b i) (𝟙 Y) y J) :
    ∃ c : Γ(Y, ⊤), ∀ i (y : Y) (J), Good L y J →
      sval (a i) (𝟙 Y) y J = gs (𝟙 Y) y ⊤ c * sval (b i) (𝟙 Y) y J := by

  let W : Ix × (K → L.ι) → Y.Opens := fun p => Y.basicOpen ((b p.1).f p.2)
  choose q hq using fun p : Ix × (K → L.ι) => exists_quot ((a p.1).f p.2) ((b p.1).f p.2)
  have goodAt : ∀ y : Y, ∃ J, Good L y J := fun y => by
    obtain ⟨J, hJ, -⟩ := exists_good L hL y (K := Empty) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim)
    exact ⟨J, hJ⟩

  have loc : ∀ p (y : Y), y ∈ W p → ∀ J, Good L y J →
      gs (𝟙 Y) y (W p) (q p) * sval (b p.1) (𝟙 Y) y J = sval (a p.1) (𝟙 Y) y J ∧
        IsUnit (sval (b p.1) (𝟙 Y) y J) := by
    intro p y hy J hJ
    have hyc : y ∈ (LB.LinComb L φ ε).U p.2 := Y.basicOpen_le _ hy
    have e := hq p y hy
    rw [gs_id_linComb_eq_trF_mul_sval (b p.1) p.2 y hyc J hJ, gs_id_linComb_eq_trF_mul_sval (a p.1) p.2 y hyc J hJ] at e
    have hu := (mem_basicOpen_iff_gs ((b p.1).f p.2) y hyc).1 hy
    rw [gs_id_linComb_eq_trF_mul_sval (b p.1) p.2 y hyc J hJ] at hu
    set T := trF φ ε (𝟙 Y) y p.2 (fun k => J (𝟙 Y ≫ φ k))
    refine ⟨?_, isUnit_of_mul_isUnit_right hu⟩
    apply T.isUnit.mul_left_cancel
    linear_combination e
  obtain ⟨c, hc⟩ := exists_global_unit_of_compatible_of_iSup_eq W (fun y => by
      obtain ⟨J, hJ⟩ := goodAt y
      obtain ⟨i, hi⟩ := hb y J hJ
      exact ⟨(i, fun k => J (𝟙 Y ≫ φ k)),
        (mem_basicOpen_iff_gs ((b i).f _) y (hJ.mem φ (𝟙 Y))).2 hi⟩) q
    (fun p p' y hy hy' => by
      obtain ⟨J, hJ⟩ := goodAt y
      obtain ⟨e1, u1⟩ := loc p y hy J hJ
      obtain ⟨e2, u2⟩ := loc p' y hy' J hJ
      have e3 := hab p.1 p'.1 y J hJ
      apply (u1.mul u2).mul_right_cancel
      linear_combination sval (b p'.1) (𝟙 Y) y J * e1 + e3 - sval (b p.1) (𝟙 Y) y J * e2)
  refine ⟨c, fun i y J hJ => ?_⟩
  obtain ⟨i₀, h₀⟩ := hb y J hJ
  have hy₀ : y ∈ W (i₀, fun k => J (𝟙 Y ≫ φ k)) :=
    (mem_basicOpen_iff_gs ((b i₀).f _) y (hJ.mem φ (𝟙 Y))).2 h₀
  obtain ⟨e1, -⟩ := loc _ y hy₀ J hJ
  rw [hc _ y hy₀]
  apply h₀.mul_right_cancel
  linear_combination hab i i₀ y J hJ - sval (b i) (𝟙 Y) y J * e1

theorem ratio_glue : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ K₃ : Type) [Fintype K₁] [Fintype K₂] [Fintype K₃] (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (φ₃ : K₃ → (Y ⟶ X)) (ε₃ : K₃ → ℤ) (h : Y ⟶ Y), Geo.Tor.FormEq φ₁ ε₁ (Sum.elim (fun k => h ≫ φ₂ k) φ₃) (Sum.elim ε₂ ε₃) → ∀ (u : LB.Gen (LB.LinComb L φ₃ ε₃)), u.IsGen → ∀ (Ix : Type) (s'' : Ix → LB.Sec (LB.LinComb L φ₁ ε₁)) (s : Ix → LB.Sec (LB.LinComb L φ₂ ε₂)), (∀ (y : Y) (J), Geo.Tor.Good L y J → ∃ i, IsUnit (Geo.Tor.sval (s i) h y J)) → (∀ i i' (y : Y) (J), Geo.Tor.Good L y J → Geo.Tor.sval (s'' i) (𝟙 Y) y J * Geo.Tor.sval (s i') h y J = Geo.Tor.sval (s'' i') (𝟙 Y) y J * Geo.Tor.sval (s i) h y J) → ∃ c : Γ(Y, ⊤), ∀ i (y : Y) (J), Geo.Tor.Good L y J → Geo.Tor.sval (s'' i) (𝟙 Y) y J = Geo.Tor.gs (𝟙 Y) y ⊤ c * (Geo.Tor.sval (s i) h y J * (Geo.Tor.val u (𝟙 Y) y J).val) := by
  intro X Y L hL K₁ K₂ K₃ _ _ _ φ₁ ε₁ φ₂ ε₂ φ₃ ε₃ h hF u hu Ix s'' s hs hx
  have hF' : Geo.Tor.FormEq (Sum.elim (fun k => h ≫ φ₂ k) φ₃) (Sum.elim ε₂ ε₃) φ₁ ε₁ :=
    fun U _ g => (hF U g).symm
  choose b hb using fun i => Geo.Tor.exists_sec hL hF' (Geo.Tor.pullMulSec (s i) h u hu)
  have key : ∀ i (y : Y) (J), Geo.Tor.Good L y J →
      Geo.Tor.sval (b i) (𝟙 Y) y J = Geo.Tor.sval (s i) h y J * (Geo.Tor.val u (𝟙 Y) y J).val := by
    intro i y J hJ
    rw [hb i Y (𝟙 Y) y J hJ, Geo.Tor.sval_pullMulSec (s i) h u hu (𝟙 Y) y hJ, Category.id_comp]
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.SectionRatio.exists_ratio hL s'' b
    (fun y J hJ => by
      obtain ⟨i, hi⟩ := hs y J hJ
      exact ⟨i, by rw [key i y J hJ]; exact hi.mul (Geo.Tor.val u (𝟙 Y) y J).isUnit⟩)
    (fun i i' y J hJ => by
      rw [key i y J hJ, key i' y J hJ]
      linear_combination (Geo.Tor.val u (𝟙 Y) y J).val * hx i i' y J hJ)
  refine ⟨c, fun i y J hJ => ?_⟩
  rw [hc i y J hJ, key i y J hJ]

end GlobalTheory.SectionRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitValue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

lemma eSec_pullback_fst {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    eSec ((Over.pullback p).obj G) ≫ pullback.fst G.hom p = p ≫ eSec G := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

lemma krull_ext {V : Type} [CommRing V] [IsNoetherianRing V] [IsLocalRing V]
    (W : (Spec (CommRingCat.of V)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of V), W))
    (h : ∀ (e : ℕ) (z), gs (thick V (maximalIdeal V) e) z W a = gs (thick V (maximalIdeal V) e) z W b) :
    a = b := by
  subst hW
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).hom).1
  apply hinj
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top, Ideal.mem_iInf]
  intro e
  refine Ideal.pow_le_pow_right (Nat.le_succ e) (Ideal.Quotient.eq.1 ?_)
  have key : ((thick V (maximalIdeal V) e).app ⊤).hom a = ((thick V (maximalIdeal V) e).app ⊤).hom b := by
    refine fn_ext fun z hz => ?_
    rw [gs_pull _ _ z ⊤ trivial, gs_pull _ _ z ⊤ trivial, Category.id_comp]
    exact h e z
  have nat := fun x => congrArg (fun φ => φ.hom x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  exact (nat a).symm.trans ((congrArg _ key).trans (nat b))

lemma trF_unique {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] [Unique K] (φ : Y ⟶ X) (n : ℤ) (r : Z ⟶ Y)
    (z : Z) (J : (Z ⟶ X) → L.ι) (j : L.ι) (q : Z ⟶ X) (hq : r ≫ φ = q) :
    trF (L := L) (fun _ : K => φ) (fun _ => n) r z (fun _ => J (r ≫ φ)) (fun _ => j) =
      gm q z (L.U (J q) ⊓ L.U j) (L.g (J q) j) ^ n := by
  subst hq
  exact Fintype.prod_unique _

def thU (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) :
    (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
  thick R I e

section Thick

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ)

lemma eSec_fGl : eSec (thickObj R I e G) ≫ fGl I G e = thU R I e ≫ eSec G :=
  eSec_pullback_fst _ _

lemma eSec_pGl : eSec (thickObj R I e G) ≫ pGl U e = thU R I e ≫ eSec D.toPre.P.A := by
  have := (U.gt e).q_hom
  have h1 : (η[thickObj R I e G] ≫ (U.gt e).q) = η[thickObj R I e D.toPre.P.A] := IsMonHom.one_hom _
  have h2 : eSec (thickObj R I e G) ≫ (U.gt e).q.left = eSec (thickObj R I e D.toPre.P.A) :=
    congrArg Over.Hom.left h1
  refine Eq.trans ?_ (eSec_pullback_fst (thick R I e) _)
  rw [← h2, Category.assoc]
  rfl

lemma eSec_map (f : G ⟶ G) [IsMonHom f] :
    eSec (thickObj R I e G) ≫ ((Over.pullback (thick R I e)).map f).left = eSec (thickObj R I e G) :=
  congrArg Over.Hom.left (IsMonHom.one_hom ((Over.pullback (thick R I e)).map f))

lemma wv_rig (z : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
    (hM : (thU R I e ≫ eSec D.toPre.P.A) z ∈ D.toPre.P.L.U jM) (hL : (thU R I e ≫ eSec G) z ∈ U.LG.L.U jL) :
    wv U e (eSec (thickObj R I e G)) z jM jL *
      gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => jL)) (U.LG.rig.s (fun _ => jL)) =
      gm (thU R I e) z ((D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM)) (D.toPre.rig.s (fun _ => jM)) := by
  have m₁ : z ∈ eSec (thickObj R I e G) ⁻¹ᵁ ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL)) :=
    ⟨mem_pull.2 ((congrArg (fun g => g z ∈ D.toPre.P.L.U jM) (eSec_pGl U e)).mpr hM),
      mem_pull.2 ((congrArg (fun g => g z ∈ U.LG.L.U jL) (eSec_fGl (G := G) e)).mpr hL)⟩
  have m₂ : z ∈ thU R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => jL) := mem_pull.2 hL
  have m₃ : z ∈ thU R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM) := mem_pull.2 hM
  have hz : z ∈ (eSec (thickObj R I e G) ⁻¹ᵁ ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL))) ⊓ thU R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => jL) ⊓
      thU R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM) := ⟨⟨m₁, m₂⟩, m₃⟩
  have W := congrArg (gm (𝟙 _) z _) (U.w_rig e (fun _ => jM, fun _ => jL) _
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ _ z _ _ _ hz _) (gm_rp₁ _ z _ _ _ hz _))).symm.trans
    (W.trans (gm_rp₁ _ z _ _ _ hz _))

lemma unit_value_thick (f : G ⟶ G) [IsMonHom f] {g : D.toPre.P.A.left ⟶ D.toPre.P.A.left} {N : ℕ} (hN : 0 < N)
    {ε : Fin 2 → ℤ} (X : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, g] ε))
    (hX : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (eSec D.toPre.P.A))
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (1 * (N - 1))))
    (k : ℕ) (σ'' : H0 U.LG.L (k * N)) (τ : H0 U.LG.L k)
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J → ∀ jL jL',
      (r ≫ fGl I G e) z ∈ U.LG.L.U jL →
      ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ fGl I G e) z ∈ U.LG.L.U jL' →
      (wv U e r z (J (r ≫ pGl U e)) jL ^ (k * N)).val * sv U (k * N) σ'' (r ≫ fGl I G e) z jL =
        (val X (r ≫ pGl U e) z J ^ k).val *
          ((wv U e (r ≫ ((Over.pullback (thick R I e)).map f).left) z
            (J ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ pGl U e)) jL' ^ k).val *
            sv U k τ ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ fGl I G e) z jL'))
    (z : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left) (j : U.LG.L.ι)
    (hj : (thU R I e ≫ eSec G) z ∈ U.LG.L.U j) :
    sv U (k * N) σ'' (thU R I e ≫ eSec G) z j =
      (gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => j)) (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        sv U k τ (thU R I e ≫ eSec G) z j := by
  choose J hJ using fun ψ : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left ⟶ D.toPre.P.A.left =>
    exists_chart D.toPre.P.isLB (ψ z)
  have hJ : Good D.toPre.P.L z J := hJ
  have E := H _ (eSec (thickObj R I e G)) z J hJ j j (by rw [eSec_fGl]; exact hj)
    (by rw [eSec_map, eSec_fGl]; exact hj)
  rw [eSec_map, eSec_fGl, eSec_pGl] at E
  have hw := wv_rig U e z _ j (hJ (thU R I e ≫ eSec D.toPre.P.A)) hj
  have hx : val X (thU R I e ≫ eSec D.toPre.P.A) z J =
      gm (thU R I e) z ((D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => J (thU R I e ≫ eSec D.toPre.P.A)))
        (D.toPre.rig.s (fun _ => J (thU R I e ≫ eSec D.toPre.P.A))) ^ (1 * (N - 1)) :=
    (val_pull hJ X _ _).symm.trans ((val_corr hJ hX _).trans (map_pow _ _ _))
  rw [hx, ← hw] at E
  generalize wv U e (eSec (thickObj R I e G)) z (J (thU R I e ≫ eSec D.toPre.P.A)) j = w at E
  generalize gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => j)) (U.LG.rig.s (fun _ => j)) = u at E ⊢
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  refine (w ^ (k * (n + 1))).mul_right_inj.1 (E.trans ?_)
  simp only [Nat.add_sub_cancel, Units.val_pow_eq_pow_val, Units.val_mul]
  ring

end Thick

theorem unit_value {V : Type} [CommRing V] [IsDomain V] [IsNoetherianRing V] [IsLocalRing V]
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
    {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    (U : UnifPre (maximalIdeal V) D A G) {N : ℕ} (hN : 0 < N) (k : ℕ) (σ'' : H0 U.LG.L (k * N)) (τ : H0 U.LG.L k)
    (H : ∀ (e : ℕ) (z) (j : U.LG.L.ι), (thU V (maximalIdeal V) e ≫ eSec G) z ∈ U.LG.L.U j →
      sv U (k * N) σ'' (thU V (maximalIdeal V) e ≫ eSec G) z j =
      (gm (thU V (maximalIdeal V) e) z ((U.LG.L.pull (eSec G)).U (fun _ => j))
        (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val * sv U k τ (thU V (maximalIdeal V) e ≫ eSec G) z j)
    (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (J) (hJ : Good U.LG.L y J) :
    sval σ'' (r ≫ eSec G) y J =
      (val (L := U.LG.L) U.LG.rig r y J ^ (k * (N - 1))).val * sval τ (r ≫ eSec G) y J := by
  obtain ⟨j, hj⟩ := exists_chart U.LG.isLB (eSec G (IsLocalRing.closedPoint V))
  have hj' : ∀ x, eSec G x ∈ U.LG.L.U j := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := V) x).map (eSec G).continuous).mem_open (U.LG.L.U j).isOpen hj
  let W₁ : G.left.Opens := LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j)
  have m₁ : ∀ x, eSec G x ∈ W₁ := fun x => Set.mem_iInter.2 fun _ => hj' x
  let W : (𝟙_ (Over (Spec (CommRingCat.of V)))).left.Opens := (U.LG.L.pull (eSec G)).U (fun _ => j)
  have m : ∀ x, x ∈ W := fun x => mem_pull.2 (hj' x)
  have hle : W ≤ eSec G ⁻¹ᵁ W₁ := fun x _ => m₁ x
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (s : Γ(G.left, W₁)),
      gs r y W (rs hle (((eSec G).app W₁).hom s)) = gs (r ≫ eSec G) y W₁ s := fun Z r y s =>
    (gs_res r y hle (m _) _).trans (gs_pull r (eSec G) y W₁ (m₁ _) s)
  have ev' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z),
      gs r y W ((@id Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, W)ˣ (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        rs hle (((eSec G).app W₁).hom (τ.f (fun _ => j)))) =
      (gm r y W (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val * sv U k τ (r ≫ eSec G) y j := fun Z r y =>
    (gs_mul r y W (m _) _ _).trans (congrArg₂ (· * ·) ((gs_unit r y W (m _) _).trans
      (congrArg Units.val (map_pow _ _ _))) (ev Z r y _))
  have key : rs hle (((eSec G).app W₁).hom (σ''.f (fun _ => j))) =
      (@id Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, W)ˣ (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        rs hle (((eSec G).app W₁).hom (τ.f (fun _ => j))) :=
    krull_ext W (eq_top_iff.2 fun x _ => m x) _ _ fun e z =>
      (ev _ (thU V (maximalIdeal V) e) z _).trans ((H e z j (hj' _)).trans (ev' _ (thU V (maximalIdeal V) e) z).symm)
  have E := (ev Z r y _).symm.trans ((congrArg (gs r y W) key).trans (ev' Z r y))
  have a₁ : sval σ'' (r ≫ eSec G) y J = _ :=
    sec_trans σ'' (r ≫ eSec G) y (hJ.mem _ (r ≫ eSec G)) (j' := fun _ => j) (m₁ _)
  have a₂ : sval τ (r ≫ eSec G) y J = _ :=
    sec_trans τ (r ≫ eSec G) y (hJ.mem _ (r ≫ eSec G)) (j' := fun _ => j) (m₁ _)
  have a₃ : val (L := U.LG.L) U.LG.rig r y J = _ :=
    gen_trans (L := U.LG.L) U.LG.rigGen r y (hJ.mem _ r) (j' := fun _ => j) (m _)
  rw [a₁, a₂, a₃]
  refine (congrArg _ E).trans ?_
  rw [trF_unique _ _ _ _ J j (r ≫ eSec G) (Category.comp_id _), trF_unique _ _ _ _ J j (r ≫ eSec G) (Category.comp_id _),
    trF_unique _ _ _ _ J j (r ≫ eSec G) rfl]
  simp only [zpow_natCast, zpow_one]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have alg : ∀ (c u : (Z.presheaf.stalk y)ˣ) (s : Z.presheaf.stalk y), (c ^ (k * (n + 1))).val * ((u ^ (k * n)).val * s) =
      ((c * u) ^ (k * n)).val * ((c ^ k).val * s) := fun c u s => by
    simp only [Units.val_pow_eq_pow_val, Units.val_mul]
    ring
  exact alg _ _ _

theorem value_at_unit_section : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])), X.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ X (eSec P.D.toPre.P.A)) (GeneratorPullback.powGen P.D.toPre.P.L _ _ P.D.toPre.rig (1 * (N - 1))) → ∀ (k : ℕ) (σ'' : H0 P.U.LG.L (k * N)) (τ : H0 P.U.LG.L k), (∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k * N)).val * sv P.U.toUnifPre (k * N) σ'' (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k).val * sv P.U.toUnifPre k τ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval σ'' (r ≫ eSec t.G) y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig r y J ^ (k * (N - 1))).val * Geo.Tor.sval τ (r ≫ eSec t.G) y J := by
  intro V _ _ _ E _ _ _ H t P a N _ hN X _ hX k σ'' τ h
  have := t.act.hom a
  exact unit_value P.U.toUnifPre hN k σ'' τ fun e => unit_value_thick P.U.toUnifPre e (t.act.act a) hN X hX k σ'' τ (h e)

end GlobalTheory.UnitValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VanishOfTermsVanish
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClosedFibreTerm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem vanish_of_terms_vanish {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
    (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (h : U.ExpandsAt e k σ f)
    (h0 : ∀ α j, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0) (j) :
    ((fstG I e G).left.app _).hom (σ.f j) = 0 := by
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f h
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  refine fn_ext fun y hy => ?_
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have H := (hS _ (𝟙 _) y J hJ).2 jL (Set.mem_iInter.1 hy 0)
  have hz : ∀ α, sval (f α) (𝟙 _ ≫ pGl U e) y J = 0 := fun α => by
    have m := hJ.mem (D.toPre.famφB α) (𝟙 _ ≫ pGl U e)
    exact (gs_pull (𝟙 _) _ y _ m _).symm.trans ((congrArg (gs (𝟙 _) y _) (h0 α _)).trans (gs_zero (𝟙 _) y _ m))
  rw [Finset.sum_eq_zero fun α _ => by rw [hz α, zero_mul]] at H
  exact (gs_pull (𝟙 _) _ y _ hy _).trans (((Units.mul_right_eq_zero _).1 H).trans (gs_zero (𝟙 _) y _ hy).symm)

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (σ : H0 U.LG.L 1) (g : ∀ α : D.toPre.X, D.toPre.SecB 1 α), U.ExpandsAt 0 1 σ g → (∀ χ, χ ≠ 0 → ∃ g' : D.toPre.SecB 1 χ, SecIsMul D.toPre.P.A.hom ϖ (g χ) g') → ((∃ j, ((fstG (maximalIdeal V) 0 G).left.app _).hom (σ.f j) ≠ 0) ↔ ¬ ∃ g' : D.toPre.SecB 1 0, SecIsMul D.toPre.P.A.hom ϖ (g 0) g') := by
  intro V _ _ _ ϖ hϖ D A G _ _ U σ g hE hχ
  have Q : ∀ α : D.toPre.X, (∀ j, ((U.gt 0).pG.left.app _).hom ((g α).f j) = 0) ↔
      ∃ g' : D.toPre.SecB 1 α, SecIsMul D.toPre.P.A.hom ϖ (g α) g' := fun α => by
    have := GlobalTheory.ExtDiv.main V ϖ hϖ D A G U 0 1 α (g α)
    have hp : ϖ ^ (0 + 1) = ϖ := pow_one ϖ
    rwa [hp] at this
  rw [← not_forall]
  refine not_congr ⟨fun h => (Q 0).1 (WeightPf.weightIndep V _ D A G U 0 1 σ g h hE 0), fun h => ?_⟩
  refine vanish_of_terms_vanish U 0 1 σ g hE fun α => (Q α).2 ?_
  by_cases hα : α = 0
  · subst hα; exact h
  · exact hχ α hα

end GlobalTheory.ClosedFibreTerm
end

