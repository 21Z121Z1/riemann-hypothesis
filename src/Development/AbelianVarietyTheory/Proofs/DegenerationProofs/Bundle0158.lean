import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraitSectionBasisDescendsFiniteDvrExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreImageTestIndependent
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TestFib

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE} {p : ℕ} [Fact p.Prime]

theorem level_ne_zero (S : ThetaSys o Ω) (y : Sp (OO p) ⟶ M.Z) : ((S.r * S.N : ℕ) : kb p) ≠ 0 := by
  have h := S.unit.map (Spec.preimage (rPt p ≫ y ≫ M.s)).hom
  rw [map_natCast] at h
  exact h.ne_zero

variable {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u}

abbrev mb (tm : Q.TMap t c) : Matrix S.J S.J (kb p) :=
  tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)

theorem isUnit_det_mb (tm : Q.TMap t c) : IsUnit (mb tm).det := by
  have h := tm.unit.map ((IsLocalRing.residue (OO p)).comp t.u.j)
  rw [RingHom.map_det] at h
  exact h

theorem crd_image (tm : Q.TMap t c) (x₀ : Sp (kb p) ⟶ t.mod.Φ.G.left) (hx : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _)
    (v : S.J → kb p) (hv : Crd (t.mod.Φ.H 1) t.mod.F x₀ v) :
    (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧
      Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) ((x₀ ≫ t.mod.r) ≫ tm.f) ((mb tm).mulVec v) := by
  have h1 : (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j := by
    rw [Category.assoc, t.mod.cart.1.w, ← Category.assoc, hx]
    exact Category.id_comp _
  refine ⟨h1, tm.crd (kb p) ((IsLocalRing.residue (OO p)).comp t.u.j) _ v (h1.trans ?_)
    (t.mod.red (Over.homMk x₀ hx) v hv)⟩
  exact (Spec.map_comp _ _).symm

theorem image_over (tm : Q.TMap t c) (c' : Sp (kb p) ⟶ t.u.G.left) (h : c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j) :
    (c' ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := by
  rw [Category.assoc, tm.f_over, ← Category.assoc, h, Category.assoc, c.fac]

theorem mem_cone_iff [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (hB : BaseFacts S M U₀ EE) (tm : Q.TMap t c) (hS : S.Big)
    (v : S.J → kb p) :
    v ∈ cone t.mod.Φ.G.hom (t.mod.Φ.H 1) t.mod.F ↔ (∃ i, t.cls i = 0 ∧ v i ≠ 0) ∧
      ∀ (d : ℕ) (Pf : MvPolynomial S.J (kb p)), d ≤ S.N ^ S.g * S.g.factorial → Pf.IsHomogeneous d →
        (∀ w ∈ Q.Tors (rPt p ≫ y) tm.l, MvPolynomial.eval w Pf = 0) →
        MvPolynomial.eval ((mb tm).mulVec v) Pf = 0 := by
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hsm : SmoothOfRelativeDimension S.g t.mod.Φ.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback t.mod.cart.1 t.mod.smooth
  have hbig : Big S.g S.N (S.r * S.N) := ⟨(GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre hL o Ω S ρ p y₀ t.u).2.2.2.1, hS.1, hS.2.1⟩
  have key := GlobalTheory.T.mem_torusExtensionCone_iff_smallDegreeForms hL.1 hL.2.1 (kb p) t.mod.Φ S.g S.N (S.r * S.N) _ S.J _ t.mod.F t.mod.pol hbig
    t.mod.good t.mod.dim (level_ne_zero S y) hsm
    (fun d hd => (Mod.hilb_special_le_generic p _ _ _ _ _ 0 _ _ _ _ _ _ t.mod d).trans
      (GlobalTheory.T.degreeFormsDimension_genericFibre_le hL o Ω S ρ p y₀ t.u S.J t.σ d hd)) v
  obtain ⟨T₁, T₂⟩ := GlobalTheory.T.torsionPoints_specialFibre_supportCoordinates hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS
  have hinv : ∀ w, (mb tm)⁻¹.mulVec ((mb tm).mulVec w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_mb tm), Matrix.one_mulVec]
  refine key.trans (and_congr (exists_congr fun i => and_congr (map_eq_zero_iff _ t.mod.xe.symm.injective) Iff.rfl)
    ⟨fun H d Pf hd hPf hT => ?_, fun H d Pf hd hPf hT => ?_⟩)
  · obtain ⟨F, hF, hev⟩ := InFibChart.exists_subst (mb tm) hPf
    rw [← hev]
    refine H d F hd hF fun x hx => ?_
    obtain ⟨w, hw, hw'⟩ := T₁ x hx
    exact ⟨w, hw, (hev w).trans (hT _ hw')⟩
  · obtain ⟨F, hF, hev⟩ := InFibChart.exists_subst (mb tm)⁻¹ hPf
    rw [← hinv v, ← hev]
    refine H d F hd hF fun w hw => ?_
    obtain ⟨x, w₀, hx, hw₀, rfl⟩ := T₂ w hw
    obtain ⟨w₁, hw₁, h0⟩ := hT x hx
    obtain ⟨u, hu⟩ := CrdCalc.crd_unique hw₁ hw₀
    rw [hev, hinv, show w₀ = fun j => (u : kb p) * w₁ j from funext hu, InFibChart.eval_scale _ _ hPf, h0, mul_zero]

theorem image_special_fibre_iff : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ x : Sp (kb p) ⟶ Q.P.left, x ≫ Q.P.hom = rPt p ≫ y → ((∃ c' : Sp (kb p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x) ↔ (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS x hx
  constructor
  · rintro ⟨c', hc', rfl⟩
    let x₀ : Sp (kb p) ⟶ t.mod.Φ.G.left := t.mod.cart.1.lift c' (𝟙 _) (hc'.trans (Category.id_comp _).symm)
    have h₁ : x₀ ≫ t.mod.r = c' := t.mod.cart.1.lift_fst _ _ _
    have h₂ : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _ := t.mod.cart.1.lift_snd _ _ _
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists (t.mod.Φ.H_isLB 1) t.mod.F x₀
    have hcr := (crd_image tm x₀ h₂ v hv).2
    rw [h₁] at hcr
    have hov := image_over tm c' hc'
    obtain ⟨k₁, k₂⟩ := (mem_cone_iff hL hB tm hS v).1 ⟨x₀, h₂, hv⟩
    rw [← Category.assoc]
    refine ⟨(GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS _ v hov hcr).2 k₁,
      InFibChart.inFib_of_chart o Ω S ρ M U₀ EE hB Q _ tm.l _ _ hcr ?_⟩
    rw [hov]
    exact k₂
  · rintro ⟨hG, hF⟩
    obtain ⟨x', rfl⟩ : ∃ x' : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme, x' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x := by
      refine ⟨IsOpenImmersion.lift _ x ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      have e : Q.P.hom (x w) = y (rPt p w) :=
        (Scheme.Hom.comp_apply _ _ _).symm.trans
          ((congrArg (fun f : Sp (kb p) ⟶ M.Z => f w) hx).trans (Scheme.Hom.comp_apply _ _ _))
      show Q.P.hom (x w) ∈ Q.W tm.l
      rw [e]
      exact ((IsLocalRing.specializes_closedPoint (rPt p w)).map y.continuous).mem_open (Q.W tm.l).isOpen tm.mem
    have hLB : (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι).IsLB := LB.isLB_pull Q.isLB _
    obtain ⟨w, hw⟩ := CrdCalc.crd_exists hLB (Q.σ tm.l) x'
    obtain ⟨v, rfl⟩ : ∃ v, (mb tm).mulVec v = w := ⟨(mb tm)⁻¹.mulVec w, by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_mb tm), Matrix.one_mulVec]⟩
    have hx' : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := (Category.assoc _ _ _).symm.trans hx
    have k₂ := hF tm.l x' _ rfl hw
    rw [hx] at k₂
    obtain ⟨x₀, h₂, hv⟩ := (mem_cone_iff hL hB tm hS v).2
      ⟨(GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS x' v hx' hw).1 hG, k₂⟩
    obtain ⟨h₁, hcr⟩ := crd_image tm x₀ h₂ v hv
    refine ⟨x₀ ≫ t.mod.r, h₁, ?_⟩
    have e : ((x₀ ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ∣_ Q.W tm.l) = x' ≫ (Q.P.hom ∣_ Q.W tm.l) := by
      rw [← cancel_mono (Q.W tm.l).ι, Category.assoc, Category.assoc x', morphismRestrict_ι, hx']
      exact image_over tm _ h₁
    rw [← Category.assoc, ImmSep.eq_of_crd_eq _ _ _ _ _ _ _ hLB (Q.imm tm.l) (kb p) _ x' _
      (by rw [← Category.assoc, e, Category.assoc]) hcr hw]

end GlobalTheory.ZH.TestFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionsIndependentOnClosedFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.IndepFib

theorem eq_zero_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → GlobalTheory.ZH.valR x U f = 0) : f = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  have hne' : ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => hne (SetLike.coe_injective e)
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hne' (X.basicOpen f).isOpen.isLocallyClosed
  have hb : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ X.basicOpen f := fun q _ => by
    show pointOfClosedPoint π y hc q ∈ X.basicOpen f
    rw [pointOfClosedPoint_apply π y hc q]
    exact hy
  have hU : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le f))
  exact ((CrdCalc.isUnit_valR_iff _ U hU f).2 hb).ne_zero (h _ (pointOfClosedPoint_comp π y hc) hU)

theorem lin_eq_zero {k : Type} [Field k] [IsAlgClosed k] (Φ : FibPre k) [Smooth Φ.G.hom] {N : ℕ}
    {q : QuadraticMap ℤ Φ.E.X ℝ} {J : Type} [Fintype J] {cls : J → Φ.E.X} {F : J → (Φ.H 1).Sec}
    (hG : Φ.Good N q cls F) (a : J → k) (h : ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, ∑ i, a i * v i = 0) : a = 0 := by
  have : IsReduced Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced Φ.G.hom
  refine GlobalTheory.ZH.WtLin.linIndep k Φ N q J cls F hG a fun l => ?_
  refine eq_zero_of_points Φ.G.hom _ _ fun x hx hU => ?_
  have h1 := h _ ⟨x, hx, l, 1, hU, fun _ => rfl⟩
  rw [CrdCalc.valR_eq x _ hU, map_sum, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, Units.val_one, _root_.one_mul]
  exact congrArg (· * _) (GlobalTheory.Points.valR_constFn_of_section Φ.G.hom x hx _ hU (a i))

theorem change_mul_change {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type} [Fintype J]
    {A : Subalgebra o Ω} {B B' C : Matrix J J Ω} (hC : C * B' = 1) {g g' : Matrix J J A}
    (h : B' = g.map (↑) * B) (h' : B = g'.map (↑) * B') : g * g' = 1 := by
  have h1 : B' * C = 1 := mul_eq_one_comm.1 hC
  have h2 : (g.map (↑) * g'.map (↑) : Matrix J J Ω) = 1 := by
    calc (g.map (↑) * g'.map (↑) : Matrix J J Ω) = (g.map (↑) * (g'.map (↑) * B')) * C := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = 1 := by rw [← h', ← h, h1]
  ext i j
  have := congrFun (congrFun h2 i) j
  by_cases hij : i = j <;> simpa [Matrix.mul_apply, Matrix.one_apply, hij] using this

theorem indep_on_closed_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0 := by
  intro L o Ω _ _ _ _ S ρ M U₀ EE hB Q hBig hGeo l z hz hcl
  obtain ⟨hT, hC⟩ := GlobalTheory.T.exists_geometricTest_map_classicalPoint L o Ω S ρ M U₀ EE hB Q hBig hGeo
  obtain ⟨p, hp, y, hy, hyU⟩ := hC z hcl
  obtain ⟨y₀, t, c, ⟨tm⟩⟩ := hT p y hyU
  have hG := GlobalTheory.T.testModel_maps_into_openPart L o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hBig
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hx : (rPt p ≫ y) (IsLocalRing.closedPoint (kb p)) = z := by
    exact (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg y (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans hy)
  have hr : Set.range (rPt p ≫ y) = {z} := hx ▸ RatModel.range_eq_singleton _ _
  refine ⟨kb p, inferInstance, rPt p ≫ y, hr, fun a ha => ?_⟩
  have hz' : z ∈ Q.W tm.l := hy ▸ tm.mem
  obtain ⟨g, hg, -⟩ := InFibChart.exists_change Q tm.l l hz' hz
  obtain ⟨g', hg', hc'⟩ := InFibChart.exists_change Q l tm.l hz hz'
  have hgg := change_mul_change (Q.c_inv l) hg hg'
  let χ := RatModel.valHom (rPt p ≫ y) z hr
  have hGG : g.map χ * g'.map χ = 1 := by
    rw [← Matrix.map_mul, hgg, Matrix.map_one _ χ.map_zero χ.map_one]
  let ψ : t.u.V →+* kb p := (IsLocalRing.residue (OO p)).comp t.u.j
  have hψ : spMap ψ = rPt p ≫ spMap t.u.j := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have pb : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
  have hs : Smooth t.u.G.hom := t.mod.smooth.smooth
  have : Smooth t.mod.Φ.G.hom := MorphismProperty.of_isPullback pb hs
  have h0 := lin_eq_zero t.mod.Φ t.mod.good (Matrix.vecMul (Matrix.vecMul a (g.map χ)) (tm.m.map ψ)) ?_
  · have hdet : (tm.m.map ψ).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (tm.unit.map ψ).ne_zero
    have h1 := Matrix.eq_zero_of_vecMul_eq_zero hdet h0
    have h2 := congrArg (Matrix.vecMul · (g'.map χ)) h1
    simpa [Matrix.vecMul_vecMul, hGG] using h2
  rintro v ⟨x, hxs, hv⟩
  have h1 := t.mod.red (Over.homMk x hxs) v hv
  have hxG : (x ≫ t.mod.r) ≫ t.u.G.hom = spMap ψ := by
    rw [Category.assoc, pb.w, ← Category.assoc, hxs, Category.id_comp, hψ]
  have h2 := tm.crd (kb p) ψ (x ≫ t.mod.r) v hxG h1
  have hov : ((x ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := by
    rw [Category.assoc, tm.f_over, ← Category.assoc, hxG, hψ, Category.assoc, c.fac]
  obtain ⟨x', hx'⟩ : ∃ x' : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme,
      x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = ((x ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι :=
    ⟨IsOpenImmersion.lift _ _ (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      have e : Q.P.hom ((((x ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) w) = z := by
        rw [← Scheme.Hom.comp_apply, Category.assoc, hov, Subsingleton.elim w (IsLocalRing.closedPoint (kb p)), hx]
      show Q.P.hom _ ∈ Q.W l
      rw [e]
      exact hz), IsOpenImmersion.lift_fac _ _ _⟩
  have hov' : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = rPt p ≫ y := by
    rw [← Category.assoc, hx', Category.assoc, hov]
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) x'
  obtain ⟨u, hu⟩ := InFibChart.crd_change Q hB.ov.ne l tm.l x' _ (rPt p ≫ y) hx'.symm hov' hx hz hz' g' hc' hw h2
  have h3 : a ⬝ᵥ w = 0 := by
    obtain ⟨j, e, -, he⟩ := hw
    have h4 := ha x' j (by
      rw [hx', Category.assoc]
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hG (Set.mem_univ _)) hov'
    rw [dotProduct, ← mul_zero (e : kb p), ← h4, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he i, mul_left_comm]
    rfl
  have h5 : (tm.m.map ψ).mulVec v = u • (g'.map χ).mulVec w := hu
  show Matrix.vecMul (Matrix.vecMul a (g.map χ)) (tm.m.map ψ) ⬝ᵥ v = 0
  rw [← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, h5, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGG,
    Matrix.one_mulVec, dotProduct_smul, h3, smul_zero]

end GlobalTheory.ZH.IndepFib
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsProportionalSeriesMatchTorsioStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabelSystems_proportional_series_match_torsion : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), n.Prime → Odd n → (∀ (k : ℕ) (x : La), 0 < k → k • x = 0 → x = 0) → Labels N EF ζ lab → Labels N' EF ζ' lab' → (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) → (∀ k m, 0 < k → 0 < m → ζ' (k * m) ^ m = ζ' k) → (∀ j, ζ' (n ^ j) = ζ (n ^ j)) → ∀ c₀ : C, c₀ ≠ 0 → (∀ j x, N'.tx (n ^ j) (lab' _ x) = c₀ * N.tx (n ^ j) (lab _ x)) → ∃ mt : GlobalTheory.Ex.Match N N' n, ∀ j p p', mt.r (n ^ j) p p' ↔ ∃ x, N.QEq (lab _ x) p ∧ N'.QEq (lab' _ x) p' := by
  first | exact @GlobalTheory.ModelData.LabelMatch.exists_match | exact GlobalTheory.ModelData.LabelMatch.exists_match | (intros; apply GlobalTheory.ModelData.LabelMatch.exists_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsSeriesScalarIndependentOfLeveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabelSystems_series_scalar_independent_of_level : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), Odd n → Labels N EF ζ lab → Labels N' EF ζ' lab' → (∀ j, ∃ c : Cˣ, ∀ x, N'.tx (n ^ j) (lab' _ x) = c * N.tx (n ^ j) (lab _ x)) → (∃ x, N.tx (n ^ 1) (lab _ x) ≠ 0) → ∃ c₀ : C, c₀ ≠ 0 ∧ ∀ j x, N'.tx (n ^ j) (lab' _ x) = c₀ * N.tx (n ^ j) (lab _ x) := by
  first | exact @GlobalTheory.ModelData.Scalar.scalar_const | exact GlobalTheory.ModelData.Scalar.scalar_const | (intros; apply GlobalTheory.ModelData.Scalar.scalar_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionQuotientActionCompatOfRosatiValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section
namespace GlobalTheory.Relabel

theorem c_smul_val {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {N : NumD F} {O : Type} [CommRing O] [StarRing O] [Module O D.X]
    (ν : NumOf D F N) (oa : D.OAct O) (x : O) (χ : N.X) :
    N.c (ν.eX.symm (x • ν.eX χ)) = actV ν oa.onB x (N.c χ) := by
  rw [actV, ν.eA.eq_symm_apply, ν.c_eq, ν.c_eq, ν.eX.apply_symm_apply, DegPre.cF, oa.c_lin, Category.assoc]

theorem actq_cancel {F : Type} [Field F] {s s' s₀ s₀' t h₁ h₂ h₃ h₄ h₅ h₆ : Fˣ} {ρ ρ' : F}
    (e₁ : (s : F) = s₀ * ρ) (e₂ : s' * h₃ = s * t * h₅ * h₆) (e₃ : s₀' * h₄ = s₀ * t * h₁ * h₂)
    (e₄ : ρ' * (h₁ * h₂ * h₃ : Fˣ) = ρ * (h₄ * h₅ * h₆ : Fˣ)) : (s' : F) = s₀' * ρ' := by
  have a := congrArg Units.val e₂
  have b := congrArg Units.val e₃
  simp only [Units.val_mul] at a b e₄
  refine mul_right_cancel₀ (mul_ne_zero h₃.ne_zero h₄.ne_zero) ?_
  rw [e₁] at a
  linear_combination (h₄ : F) * a - ρ' * h₃ * b - (s₀ : F) * t * e₄

theorem actCompat_of_rosV : GlobalFnsSt → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → A.Bal β → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.act x y)) = x • ν'.eX (J.e y)) → (∀ (x : 𝓞 E) b, J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' oa'.onB x (J.φ b)) → (∀ a : 𝓞 E, ∃ ρ ρ', RosV A.ν A.oa.onB a ρ ∧ RosV ν' oa'.onB a ρ' ∧ ∀ b b' : A.N.A, ρ' (J.φ b) (J.φ b') * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b) * J.h b' * J.h (b * actV (N := A.N) A.ν A.oa.onB a b') : Fˣ) = ρ b b' * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b * b') * J.h b * J.h (actV (N := A.N) A.ν A.oa.onB a b') : Fˣ)) → ActCompat A.ν A.oa ν' oa' β u r J := by
  intro hG hB E _ _ _ H D
  letI := H.starRing
  intro R R' _ _ _ _ F _ _ _ _ A D' _ oa' he' hb' N' ν' k β u r J hr hbal hX hA hρ
  intro j hj x p₀ p₁ p₀' p₁' q₀ q₁ q₀' q₁' ⟨q, hqy, hqg, hqe⟩ h₀ h₁ t₀ t₁ h₀' h₁'
  obtain ⟨-, -, -, -, B⟩ := hB R A.D₀ A.even A.bimult F A.N A.ν
  obtain ⟨-, -, -, -, B'⟩ := hB R' D' he' hb' F N' ν'
  obtain ⟨τ, hτ, hτe, -⟩ := (twJ_mulEquiv F A.N N' k β u J).1 (r j) j (hr.pow hj)
  obtain ⟨qv, hqv, -⟩ := (B j).1 q
  obtain ⟨q', hq'⟩ := (B' j).2.1 (τ qv)
  have tq := (hτ qv _).1 rfl
  obtain ⟨ρ, ρ', hρ₁, hρ₂, hρ₃⟩ := hρ x
  obtain ⟨vb, vs⟩ := ((gtAct_values hG R A.D₀ F A.N A.ν (𝓞 E)).2 A.oa x ρ hρ₁ _ _ _ _ h₀.2 hqv.2).1 hqg
  have hy : qv.1.1.toAdd = A.act x q₀.1.1.toAdd := by
    rw [ArcF.act, A.ν.eX.eq_symm_apply, hqv.1, h₀.1, hqy]
  obtain ⟨P, ⟨Py, Pb, Ps⟩, Py', Pb', Ps'⟩ := tq
  obtain ⟨P₀, ⟨P₀y, P₀b, P₀s⟩, P₀y', P₀b', P₀s'⟩ := t₀
  refine ⟨q', ?_, ?_, ?_⟩
  · rw [← hq'.1, ← h₀'.1, Py', P₀y', Py, P₀y]
    exact (congrArg (fun y => ν'.eX (J.e y)) hy).trans (hX _ _)
  · refine ((gtAct_values hG R' D' F N' ν' (𝓞 E)).2 oa' x ρ' hρ₂ _ _ _ _ h₀'.2 hq'.2).2 ⟨?_, ?_⟩
    · rw [Pb', P₀b', Pb, P₀b, vb]
      exact hA _ _
    · rw [J.e.surjective.forall]
      intro (χ : A.N.X)
      have e₁ := vs χ
      have e₂ := Ps' χ
      have e₃ := P₀s' (A.act (star x) χ)
      have e₄ := hρ₃ (A.N.c χ) q₀.1.2.b
      have c₁ : (A.N.twist β u).c (A.act (star x) χ) = actV (N := A.N) A.ν A.oa.onB (star x) (A.N.c χ) :=
        c_smul_val A.ν A.oa (star x) χ
      rw [Ps, Pb, vb, hy, hbal] at e₂
      rw [P₀s, P₀b, c₁] at e₃
      have l : ν'.eX.symm (star x • ν'.eX (J.e χ)) = J.e (A.act (star x) χ) := by
        rw [ν'.eX.symm_apply_eq, hX]
      have c₂ : N'.c (J.e χ) = J.φ (A.N.c χ) := J.c_eq χ
      rw [l, c₂, P₀b', P₀b]
      exact actq_cancel e₁ e₂ e₃ e₄
  · refine ((B' j).2.2 q' p₁' _ _ hq' h₁').2 ?_
    rw [← (hτ q₁ q₁').2 t₁]
    exact (hτe _ _).1 (((B j).2.2 q p₁ _ _ hqv h₁).1 hqe)

end GlobalTheory.Relabel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionActionInValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_action_in_values : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N) (O : Type) [CommRing O] [StarRing O], (∀ (oa : D.P.OAct O) (x : O), ∃ ρ, RosV ν oa x ρ) ∧ ∀ [Module O D.X] (oa : D.OAct O) (x : O) (ρ : N.A → N.A → F), RosV ν oa.onB x ρ → ∀ g g' v v', ν.Pt g v → ν.Pt g' v' → (GtAct oa x g g' ↔ v'.b = actV ν oa.onB x v.b ∧ ∀ χ, (v'.s χ : F) = v.s (ν.eX.symm (star x • ν.eX χ)) * ρ (N.c χ) v.b) := by
  first | exact @GlobalTheory.Relabel.gtAct_values | exact GlobalTheory.Relabel.gtAct_values | (intros; apply GlobalTheory.Relabel.gtAct_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraitSectionBasisDescendsFiniteDvrExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_sectionBasis_descends_finite_dvr_extension : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left), Flat G.hom → L.IsLB → ∀ (N : ℕ) (K : Type) [Field K] (x : Sp K ⟶ Z) (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] (io : W →+* W') (io' : FractionRing W →+* FractionRing W'), io.Finite → (∀ y, io' (algebraMap W _ y) = algebraMap W' _ (io y)) → ∀ (gam : K →+* FractionRing W) (χ : Sp W ⟶ Z) (h : spMap gam ≫ x = jK W ≫ χ) (h' : spMap (io'.comp gam) ≫ x = jK W' ≫ spMap io ≫ χ) (n : ℕ) (f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))), FrameAt G L N x (io'.comp gam) (spMap io ≫ χ) h' f → FrameAt G L N x gam χ h f := by
  first | exact @GlobalTheory.OneBasis.TraitDescent.frameAt_of_finite | exact GlobalTheory.OneBasis.TraitDescent.frameAt_of_finite | (intros; apply GlobalTheory.OneBasis.TraitDescent.frameAt_of_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistIsoTorsionRepresentativeMulEquivStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_iso_torsionRepresentative_mulEquiv : ∀ (O : Type) [CommRing O] (N N' : NumD O) (k : ℕ) (β : N.Form k) (u : Oˣ) (J : NumD.Iso (N.twist β u) N'), (∀ (r : Oˣ) (j : ℕ), r ^ j = u → ∃ τ : N.QT j ≃* N'.QT j, (∀ q q', τ q = q' ↔ TwJ β u r J q q') ∧ (∀ q₁ q₂, N.QEq q₁ q₂ ↔ N'.QEq (τ q₁) (τ q₂)) ∧ ∀ q₁ q₂, N'.wp (τ q₁) (τ q₂) = N.wp q₁ q₂) ∧ ∀ (r₁ r₂ : Oˣ) (n n' m : ℕ) (q₁ : N.QT n) (q₂ : N.QT n') (q₁' : N'.QT n) (q₂' : N'.QT n'), r₂ ^ m = r₁ → q₁.1.1 = q₂.1.1 → q₁.1.2 = q₂.1.2 ^ m → TwJ β u r₁ J q₁ q₁' → TwJ β u r₂ J q₂ q₂' → q₁'.1.1 = q₂'.1.1 ∧ q₁'.1.2 = q₂'.1.2 ^ m := by
  first | exact @GlobalTheory.Relabel.twJ_mulEquiv | exact GlobalTheory.Relabel.twJ_mulEquiv | (intros; apply GlobalTheory.Relabel.twJ_mulEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationGenericFibreCartesianToModelBundleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_generic_fibre_cartesian_to_model_bundleIso : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), ∃ (w₀ : W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))), IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ∧ NormW U w₀ ρ ∧ w.IsGen ∧ IsRigidificationPullbackCompatibleIso w (jK R) ρ U.LG.rig ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : H0 U.LG.L k) (th : SecA A F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J) (J'), Good U.LG.L z J → Good A.L z J' → sval σ (r ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) z J = (wVal w z J J' (r ≫ (snd (TFK (R := R) F) A.A).left) ^ (k : ℤ)).val * VVRank.sv A.A th r z J') → ∃ σ' : U.SecGF F k, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) ∧ ∀ s, U.ExpandsG F k σ' s → U.ExpandsF F k w₀ th s := by
  first | exact @GlobalTheory.Ex.GenericFibre.exists_isoData | exact GlobalTheory.Ex.GenericFibre.exists_isoData | (intros; apply GlobalTheory.Ex.GenericFibre.exists_isoData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationOverFiniteDvrExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_over_finite_dvr_extension : ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] (i : W →+* W'), Function.Injective i → i.Finite → ∀ (ϖ : W'), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing W') F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → (∀ r : W', 0 ≤ v (algebraMap (FractionRing W') F (algebraMap W' _ r))) ∧ (∃ i' : FractionRing W →+* FractionRing W', (∀ r, i' (algebraMap W _ r) = algebraMap W' _ (i r)) ∧ ∀ a : FractionRing W, v (algebraMap (FractionRing W') F (i' a)) = 0 → ∃ u : Wˣ, algebraMap W (FractionRing W) u = a) ∧ ∀ (K : Type) [Field K] (e : K →+* F), ∃ S : ValuationSubring K, ∀ x, (x ∈ S ↔ 0 ≤ v (e x)) ∧ (S.valuation x = 1 → v (e x) = 0) := by
  first | exact @GlobalTheory.FiniteDVRValuation.main | exact GlobalTheory.FiniteDVRValuation.main | (intros; apply GlobalTheory.FiniteDVRValuation.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuesIsoCommActionAbelianPartTorsionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuesIso_comm_action_abelianPart_torsion : GlobalTheory.UT.LL → BrGtSt → AllS fun {E} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → ∀ k : ℕ, 0 < k → Labels A u r M ν' J k → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) → ∀ (x : 𝓞 E) (y y' : A.N.A), y ^ k = 1 → (letI := H.starRing; A.ν.eA y' = A.ν.eA y ≫ a.oa.onB.act x → ν'.eA (J.φ y') = ν'.eA (J.φ y) ≫ M.P.oD.onB.act x) := by
  first | exact @GlobalTheory.Ex.ActPt.main | exact GlobalTheory.Ex.ActPt.main | (intros; apply GlobalTheory.Ex.ActPt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuesIsoRespectsEndomorphismOfTorsionCompatStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuesIso_respects_endomorphism_of_torsion_compat : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (I : NumB.Iso N.toNumB N'.toNumB), GeoIso ν ν' I → ∀ (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (n : ℕ), n.Prime → (n : F) ≠ 0 → ∀ x : O, (∀ (j : ℕ) (b : N.A), b ^ n ^ j = 1 → I.φ (actV ν oa x b) = actV ν' oa' x (I.φ b)) → ∀ b, I.φ (actV ν oa x b) = actV ν' oa' x (I.φ b) := by
  first | exact @GlobalTheory.Relabel.actV_compat_of_torsion | exact GlobalTheory.Relabel.actV_compat_of_torsion | (intros; apply GlobalTheory.Relabel.actV_compat_of_torsion <;> assumption)
end

