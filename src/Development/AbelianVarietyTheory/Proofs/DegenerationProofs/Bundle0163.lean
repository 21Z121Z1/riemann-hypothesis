import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreTorsionEqReductions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaPullbackNonzeroOnClosedFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ThetaFibre

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem proj_mulVec_mem (hB : BaseFacts S M U₀ EE) (z : M.Z) {v : S.J → Ω} (hv : v ∈ EE.E z) :
    ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v ∈ EE.E z := by
  have hT : S.TT M z ≤ S.HH M z := (hB.free z).2 ▸ (hB.free z).1.1
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have := Fintype.ofFinite (S.TT M z)
  have e : ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v =
      algebraMap o (M.O z) (Ring.inverse (Nat.card (S.TT M z) : o)) •
        ∑ t : S.TT M z, ((S.ρ t).map (algebraMap o Ω)).mulVec v := by
    ext i
    simp [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.mulVec, dotProduct, Matrix.sum_apply,
      Algebra.smul_def (A := Ω), Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t _ => hB.stab z _ (hT t.2) v hv)

theorem proj_mulVec_regular (hB : BaseFacts S M U₀ EE) {z : M.Z} (hz : IsClosed ({z} : Set M.Z))
    {v : S.J → Ω} (hv : v ∈ EE.E z) (j : S.J) :
    ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v j ∈ M.O z := by
  refine hB.zero z hz _ (proj_mulVec_mem hB z hv) ?_ j
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
    GlobalTheory.ThetaBound.proj_mul_proj S _ _ le_rfl (hB.free z).1.1 (hB.free z).1 0 0 fun _ => rfl]

theorem proj_col_eq_zero (hB : BaseFacts S M U₀ EE) {z : M.Z} (hz : IsClosed ({z} : Set M.Z))
    {K : Type} [Field K] (y : M.O z →+* K) (B : Matrix S.J S.J Ω) (hBm : ∀ k, B k ∈ EE.E z)
    (a : S.J → M.O z) (i : S.J) (ha : ∀ j, ∑ k, (a k : Ω) * B k j = (1 : Matrix S.J S.J Ω) i j)
    (h0 : ∀ k, y (a k) = 0) (j : S.J) :
    y (algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i)) = 0 := by
  have e : algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i) =
      ∑ k, a k * ⟨_, proj_mulVec_regular hB hz (hBm k) j⟩ := by
    apply Subtype.ext
    have h1 : ∑ m, algebraMap o Ω (S.proj (S.TT M z) 0 j m) * (1 : Matrix S.J S.J Ω) i m =
        algebraMap o Ω (S.proj (S.TT M z) 0 j i) := by
      simp [Matrix.one_apply]
    simp only [Subalgebra.coe_algebraMap, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_mul,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum]
    rw [← h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ha, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, map_sum]
  exact Finset.sum_eq_zero fun k _ => by rw [map_mul, h0, zero_mul]

theorem exists_mem_nonzeroLocus_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∃ x ∈ nonzeroLocus (Q.st ρ.i₀), x ∈ Q.G ∧ Q.P.hom x = z := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q hbig hgeo z hz
  by_contra hne
  have hzc : z ∈ ⨆ l, Q.W l := by rw [Q.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hzc
  obtain ⟨K, _, x, hx, hind⟩ := GlobalTheory.T.thetaSections_independent_on_closed_fibre hL o Ω S ρ M U₀ EE hB Q hbig hgeo l z hl hz
  have hc : (fun k => valF x (Q.W l) (Q.c l ρ.i₀ k)) = 0 := by
    refine hind _ fun g j hg hgx => ?_
    by_cases hj : ⊤ ≤ g ⁻¹ᵁ (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι).U j
    · have hw : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) g
          (fun i => valF g _ ((Q.σ l i).f j)) :=
        ⟨j, 1, hj, fun i => by rw [Units.val_one, _root_.one_mul]; rfl⟩
      have hr := Q.rel l K g _ hw
      rw [hgx] at hr
      by_contra h0
      have hu := (CrdCalc.crd_isUnit_iff ρ.i₀ hr).1 (isUnit_iff_ne_zero.2 h0)
      refine hne ⟨(g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (IsLocalRing.closedPoint K), hu (Set.mem_univ _),
        hg ⟨_, rfl⟩, ?_⟩
      have hm : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rw [hx] at hm
      rw [← hgx] at hm
      exact hm
    · exact Finset.sum_eq_zero fun i _ => mul_eq_zero_of_right _ (dif_neg hj)
  obtain ⟨j, hj⟩ := GlobalTheory.proj_zero_pullback_ne_zero hL o Ω S ρ K
    ((RatModel.valHom x z hx).comp (algebraMap o (M.O z))) _ (hB.free z).1
  refine hj (proj_col_eq_zero hB hz (RatModel.valHom x z hx) (Q.B l)
    (fun k => by rw [Q.basis l z hl]; exact Submodule.subset_span ⟨k, rfl⟩)
    (fun k => ⟨_, RatModel.valF_mem_O hl (Q.c l ρ.i₀ k)⟩) ρ.i₀
    (fun j => congrFun (congrFun (Q.c_inv l) ρ.i₀) j) (fun k => ?_) j)
  rw [RatModel.valHom_apply, RatModel.val_valF (by rw [hx]; exact Set.singleton_subset_iff.2 hl)]
  exact congrFun hc k

end GlobalTheory.ZH.ThetaFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPullback
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TorsionValue

theorem exists_torsion_pullback {B B' : Scheme.{0}} (H : Over B) [GrpObj H] (r : B' ⟶ B) (c : Over.mk r ⟶ H) (n : ℕ)
    (hc : c ^ n = 1) : ∃ c' : baseOver B' ⟶ (Over.pullback r).obj H, c' ^ n = 1 ∧
      c'.left ≫ pullback.fst H.hom r = c.left := by
  have h := isGrpPullback_pullback H r
  let c' : baseOver B' ⟶ (Over.pullback r).obj H :=
    Over.homMk (pullback.lift c.left (𝟙 B') ((Over.w c).trans (Category.id_comp r).symm)) (pullback.lift_snd _ _ _)
  have e : c'.left ≫ pullback.fst H.hom r = c.left := pullback.lift_fst _ _ _
  let U : Over.mk ((baseOver B').hom ≫ r) ⟶ Over.mk r := Over.homMk (𝟙 B') rfl
  have e₁ : pushHom h _ c' = preHom U c := Over.OverMorphism.ext (e.trans (Category.id_comp _).symm)
  have e₂ : pushHom h _ (c' ^ n) = pushHom h _ 1 := by
    rw [map_pow, e₁, ← map_pow, hc, map_one, map_one]
  refine ⟨c', ?_, e⟩
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · exact congrArg (fun z => z.left) e₂
  · rw [Over.w, Over.w]

theorem cl_of_test {C : GlobalTheory.ZJ.Core} {p : ℕ} [Fact p.Prime] {y : Sp (GlobalTheory.ZJ.OO p) ⟶ C.Z} (τ : C.Test y) : C.Cl y := by
  let k : τ.V →+* PadicAlgCl p := (GlobalTheory.ZJ.OO p).subtype.comp τ.j
  have hk : Function.Injective k := Subtype.val_injective.comp τ.j_inj
  have e : GlobalTheory.ZJ.gPt p ≫ spMap τ.j = spMap (IsFractionRing.lift (K := FractionRing τ.V) hk) ≫ jK τ.V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (IsFractionRing.lift_algebraMap (K := FractionRing τ.V) hk x).symm
  have e2 : GlobalTheory.ZJ.gPt p ≫ y = (spMap (IsFractionRing.lift (K := FractionRing τ.V) hk) ≫ τ.yK) ≫ C.U.ι := by
    rw [Category.assoc, τ.yK_fac, ← Category.assoc, ← e, Category.assoc, τ.fac]
  unfold GlobalTheory.ZJ.Core.Cl
  rw [e2]
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact ((spMap (IsFractionRing.lift (K := FractionRing τ.V) hk) ≫ τ.yK) w).2

theorem isDominant_gPt (p : ℕ) [Fact p.Prime] : IsDominant (gPt p) := by
  constructor
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (OO p).subtype).2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (OO p).subtype_injective]; exact bot_le)

theorem exists_lift {Z : Scheme.{0}} {N W : Z.Opens} (hN : N ≤ W) {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ Z)
    (hy : y (cPt p) ∈ W) (x : Sp (kb p) ⟶ N.toScheme) (hx : x ≫ N.ι = rPt p ≫ y) :
    ∃ y' : Sp (OO p) ⟶ W.toScheme, y' ≫ W.ι = y ∧ x ≫ Z.homOfLE hN = rPt p ≫ y' := by
  have hr : Set.range y ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint w).map y.continuous).mem_open W.isOpen hy
  have hy' : IsOpenImmersion.lift W.ι y hr ≫ W.ι = y := IsOpenImmersion.lift_fac _ _ _
  refine ⟨_, hy', ?_⟩
  rw [← cancel_mono W.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, hy', hx]

theorem chase {k O N W G P H H' Φ X V : Scheme.{0}} {x : k ⟶ N} {i : N ⟶ W} {h : W ⟶ G} {j : G ⟶ P} [Mono j]
    {r : k ⟶ O} {y' : O ⟶ W} {c₁ : O ⟶ X} {f : X ⟶ V} {κ : V ⟶ P} {c' : k ⟶ H'} {e : H' ⟶ Φ} {s : Φ ⟶ X}
    {q : H' ⟶ H} {g : H ⟶ G} {c : k ⟶ H} (h₁ : x ≫ i = r ≫ y') (h₂ : y' ≫ h ≫ j = c₁ ≫ f ≫ κ)
    (h₃ : r ≫ c₁ = (c' ≫ e) ≫ s) (h₄ : e ≫ s ≫ f ≫ κ = q ≫ g ≫ j) (h₅ : c' ≫ q = c) : x ≫ i ≫ h = c ≫ g := by
  rw [← cancel_mono j]
  simp only [Category.assoc] at h₃ ⊢
  rw [reassoc_of% h₁, h₂, reassoc_of% h₃, h₄, reassoc_of% h₅]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}

theorem mem_ker (t : ρ.GeoTest p y₀) {a : S.Gam} (ha : a ∈ t.l.yy.ker) : a ∈ t.τ.yy.ker := by
  obtain ⟨e, -, he⟩ := t.mt
  have := (he a 0).2 (by rw [map_zero]; exact ha)
  exact this

theorem integral_eq_section {Q : Clos ρ M U₀ EE} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u} (tm : Q.TMap t c)
    {a : S.Gam} {W : M.Z.Opens} {h : W.toScheme ⟶ Q.G.toScheme} (hh : h ≫ Q.G.ι ≫ Q.P.hom = W.ι)
    (hgen : ∀ (x : Sp (PadicAlgCl p) ⟶ W.toScheme) (x' : Sp (PadicAlgCl p) ⟶ pullback ρ.P.A.hom Q.u₀),
      x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι →
      x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left → x ≫ h ≫ Q.G.ι = x' ≫ Q.a₀)
    {y' : Sp (OO p) ⟶ W.toScheme} (hy : y' ≫ W.ι = y) {c₁ : Sp (OO p) ⟶ t.u.G.left} {a' : t.u.PtC}
    (h₁ : c₁ ≫ t.u.G.hom = spMap t.u.j) (h₂ : gPt p ≫ c₁ = t.u.toG a')
    (h₃ : t.u.toA a' = spMap y₀ ≫ (ρ.pt a).left) :
    y' ≫ h ≫ Q.G.ι = c₁ ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
  have := Q.proper
  have := isDominant_gPt p
  have e : gPt p ≫ spMap t.u.j = jFK (R := t.u.V) (PadicAlgCl p) ≫ jK t.u.V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have e₀ : jFK (R := t.u.V) (PadicAlgCl p) ≫ spMap t.u.yK = spMap y₀ := by
    refine Eq.trans ?_ (congrArg spMap t.u.fac)
    rw [← Spec.map_comp]
    rfl
  let α : Sp (PadicAlgCl p) ⟶ pullback t.u.G.hom (jK t.u.V) := a'.left
  have ha : α ≫ pullback.snd _ _ = jFK (R := t.u.V) (PadicAlgCl p) := Over.w a'
  have hs : (α ≫ tm.φ) ≫ pullback.snd _ _ = jFK (R := t.u.V) (PadicAlgCl p) ≫ c.yK := by
    rw [Category.assoc, tm.φ_snd, ← Category.assoc, ha]
  refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ (gPt p) ?_
  · simp only [Category.assoc]
    rw [hh, hy, tm.f_over, ← Category.assoc, h₁, c.fac]
  · have k := hgen (gPt p ≫ y') (α ≫ tm.φ) ?_ ?_
    · rw [Category.assoc, Category.assoc, tm.φ_f] at k
      rw [k, ← Category.assoc (gPt p), h₂]
      exact (Category.assoc _ _ _).symm
    · rw [← Category.assoc (α ≫ tm.φ), hs, Category.assoc, Category.assoc, hy, c.yK_fac, ← Category.assoc, ← e,
        Category.assoc, c.fac]
    · rw [← Category.assoc (α ≫ tm.φ), hs, Category.assoc, Category.assoc, tm.φ_fst, ← Category.assoc c.yK, c.yK_u,
        ← Category.assoc (jFK _), e₀]
      exact h₃

theorem torsSec : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → ex.core.TorsSec (S.r * S.N) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG hF z _
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  choose W h hz hh hgen using fun a : S.HH M z => GlobalTheory.T.exists_section_extending_torsionPoints_support hL o Ω S ρ M U₀ EE hB Q z a.1 a.2
  let N : M.Z.Opens := ⟨⋂ a, (W a : Set M.Z), isOpen_iInter_of_finite fun a => (W a).isOpen⟩
  have hN : ∀ a, N ≤ W a := fun a w hw => Set.mem_iInter.1 hw a
  refine ⟨N, Set.mem_iInter.2 hz, ?_⟩
  intro p _ y τ x c hy hx hc
  have hcl := cl_of_test τ
  obtain ⟨y₀, t, cf, ⟨tm⟩⟩ := (GlobalTheory.T.exists_geometricTest_map_classicalPoint hL o Ω S ρ M U₀ EE hB Q hS hG).1 p y hcl
  obtain ⟨e, he, hef⟩ := GlobalTheory.T.exists_iso_special_fibre_test_geometric_test hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t cf tm τ hS hF
  obtain ⟨c', hc', hcl'⟩ := exists_torsion_pullback τ.H _ c _ hc
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => by
    rw [cf.at_]
    exact RatModel.norm_val_le_one rfl ((M.O _).algebraMap_mem a)
  have hX : (c' ≫ e.hom) ^ (S.r * S.N) = 1 := by
    rw [← MonObj.pow_comp, hc', MonObj.one_comp]
  obtain ⟨a, ha, c₁, a', h₁, h₂, h₃, h₄⟩ :=
    (special_torsion_eq_reduction hL o Ω S ρ p y₀ t.u t.l t.σ t.cls t.mod hint).2.1 (c' ≫ e.hom) hX
  have haH : a ∈ S.HH M z := by
    rw [hB.atTest z p y y₀ t.τ ⟨hy, hcl⟩ cf.at_]
    exact mem_ker t ha
  let b : S.HH M z := ⟨a, haH⟩
  obtain ⟨y', hy', hxy⟩ := exists_lift (Z := M.Z) (hN b) y ((congrArg (· ∈ W b) hy).mpr (hz b)) x hx
  have key := integral_eq_section tm (hh b) (hgen b _) hy' h₁ h₂ h₃
  refine ⟨M.Z.homOfLE (hN b) ≫ h b, ?_, chase (j := Q.G.ι) hxy key h₄ hef hcl'⟩
  show (M.Z.homOfLE (hN b) ≫ h b) ≫ Q.G.ι ≫ Q.P.hom = N.ι
  rw [Category.assoc, hh, Scheme.homOfLE_ι]

end GlobalTheory.ZH.TorsionValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuedFieldValuationCentreLePowStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuedField_valuationCentre_le_pow : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (u : R), u ∈ IsLocalRing.maximalIdeal R → u ≠ 0 → ∀ R₁ : Subalgebra R K, Module.Finite R R₁ → ∀ S : ValuationSubring K, (∀ r, algebraMap R K r ∈ S) → ∀ e : ℕ, ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ‖gam (algebraMap R K u)‖ < 1 ∧ ∀ f ∈ R₁, S.valuation f < 1 → ‖gam f‖ < 1 ∧ (S.valuation (algebraMap R K u) = 1 → ‖gam f‖ ≤ ‖gam (algebraMap R K u)‖ ^ e) := by
  first | exact @GlobalTheory.exists_valuedField_centre_le_pow | exact GlobalTheory.exists_valuedField_centre_le_pow | (intros; apply GlobalTheory.exists_valuedField_centre_le_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisedRosatiGeneratorValuesMoveAlongIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
noncomputable section
namespace GlobalTheory.RosMove

def rosO {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) : Fin 6 → (A ⊗ A ⟶ A) :=
  ![(fst A A ≫ f) * snd A A, fst A A ≫ f, snd A A, fst A A * (snd A A ≫ g), fst A A, snd A A ≫ g]

theorem rosO_left {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) (k : Fin 6) :
    (rosO A f g k).left = rosatiφ A f g k := by
  fin_cases k <;> rfl

theorem lift_rosO {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) {T : Over S} (x y : T ⟶ A)
    (k : Fin 6) : lift x y ≫ rosO A f g k = ![(x ≫ f) * y, x ≫ f, y, x * (y ≫ g), x, y ≫ g] k := by
  fin_cases k <;> simp [rosO, MonObj.comp_mul]

theorem val_origin {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {f g : A ⟶ A}
    {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)}
    (hu : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L z J) : val u (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by
  have e : lift (1 : T ⟶ A) (1 : T ⟶ A) = toUnit T ≫ lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ hu (toUnit T).left
  rw [val_pull hJ, val_one] at this
  rw [e]; exact this

theorem val_move (hG : GlobalFnsSt) {F : Type} [Field F] [IsAlgClosed F] {S S' : Scheme.{0}} (t : Sp F ⟶ S) (t' : Sp F ⟶ S')
    {A : Over S} [GrpObj A] [IsCommMonObj A] {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] (hA : IsAbelianScheme A)
    (hA' : IsAbelianScheme A') {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (Φ : (Over.mk t ⊗ A).left ⟶ A'.left) (w : LB.Iso (L.pull (snd (Over.mk t) A).left) (L'.pull Φ)) (hw : w.IsGen)
    (hΦ : Φ ≫ A'.hom = (fst (Over.mk t) A).left ≫ t') (ψ : (Over.mk t ⟶ A) →* (Over.mk t' ⟶ A'))
    (hψ : ∀ x, (lift (𝟙 (Over.mk t)) x).left ≫ Φ = (ψ x).left) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g] (f' g' : A' ⟶ A')
    (hf : ∀ x, ψ (x ≫ f) = ψ x ≫ f') (hg : ∀ x, ψ (x ≫ g) = ψ x ≫ g')
    {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)} (hu : u.IsGen)
    (u₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L))
    {u' : LB.Gen (LB.LinComb L' (rosatiφ A' f' g') rosatiε)} (hu' : u'.IsGen)
    (u₀' : LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ u' (zero2 A')) (LB.oneGen L'))
    (z : Sp F) (N) (J) (hN : Good L z N) (hJ : Good L' z J) (b b' : Over.mk t ⟶ A) :
    val u' (lift (ψ b) (ψ b')).left z J =
      (∏ k, gw w (lift (𝟙 (Over.mk t)) (lift b b' ≫ rosO A f g k)).left z (J (ψ (lift b b' ≫ rosO A f g k)).left)
        (fun _ => N (lift b b' ≫ rosO A f g k).left) ^ rosatiε k) * val u (lift b b').left z N := by
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  let Y : Over S := T ⊗ (A ⊗ A)
  let p : Y.left ⟶ Sp F := (fst T (A ⊗ A)).left
  let Y' : Over S' := Over.mk (p ≫ t')
  let Θ : (Y ⟶ A) → (Y' ⟶ A') := fun x => Over.homMk ((lift (fst T (A ⊗ A)) x).left ≫ Φ) (by
    show ((lift (fst T (A ⊗ A)) x).left ≫ Φ) ≫ A'.hom = p ≫ t'
    rw [Category.assoc, hΦ, ← Category.assoc, ← Over.comp_left, lift_fst])
  let pt : (T ⟶ A ⊗ A) → (T' ⟶ Y') := fun c => Over.homMk (lift (𝟙 T) c).left (by
    show (lift (𝟙 T) c).left ≫ (fst T (A ⊗ A)).left ≫ t' = t'
    rw [← Category.assoc, ← Over.comp_left, lift_fst]; exact Category.id_comp _)
  have hΘ : ∀ c x, pt c ≫ Θ (snd _ _ ≫ x) = ψ (c ≫ x) := fun c x => by
    ext
    show (lift (𝟙 T) c).left ≫ (lift (fst T (A ⊗ A)) (snd _ _ ≫ x)).left ≫ Φ = _
    rw [← Category.assoc, ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, hψ]
  let H : Y' ⟶ A' ⊗ A' := lift (Θ (snd _ _ ≫ fst A A)) (Θ (snd _ _ ≫ snd A A))
  have hH : ∀ x y, pt (lift x y) ≫ H = lift (ψ x) (ψ y) := fun x y => by
    rw [comp_lift, hΘ, hΘ, lift_fst, lift_snd]
  have hr : ∀ x y k, lift (ψ x) (ψ y) ≫ rosO A' f' g' k = ψ (lift x y ≫ rosO A f g k) := fun x y k => by
    rw [lift_rosO, lift_rosO]
    fin_cases k <;> simp [hf, hg]
  have := hA.smooth
  have := hA'.proper
  have sm : Smooth (A ⊗ A).hom := by
    show Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have sp : Smooth p := by
    show Smooth (pullback.fst t (A ⊗ A).hom); infer_instance
  have rd : IsReduced Y.left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  have hE : ∀ k, (Θ (snd _ _ ≫ rosO A f g k)).left = H.left ≫ rosatiφ A' f' g' k := fun k => by
    rw [← rosO_left, ← Over.comp_left]
    refine ComplexPoints.hom_ext_of_points (X := Y.left) p A'.hom ((Over.w _).trans (Over.w _).symm) fun x hx => ?_
    let x₀ : T ⟶ Y := Over.homMk x (by
      show x ≫ Y.hom = t
      rw [← Over.w (fst T (A ⊗ A)), ← Category.assoc]
      exact (congrArg (· ≫ t) hx).trans (Category.id_comp _))
    have e : x₀ = lift (𝟙 T) (lift (x₀ ≫ snd _ _ ≫ fst A A) (x₀ ≫ snd _ _ ≫ snd A A)) := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [lift_fst]; ext; exact hx
      · rw [lift_snd, ← comp_lift, ← comp_lift, lift_fst_snd, Category.comp_id]
    have e' : x = (pt (lift (x₀ ≫ snd _ _ ≫ fst A A) (x₀ ≫ snd _ _ ≫ snd A A))).left := congrArg (·.left) e
    rw [e', ← Over.comp_left, ← Over.comp_left, hΘ, ← Category.assoc (pt _), hH, hr]
  let φ : Fin 6 → (Y.left ⟶ (T ⊗ A).left) := fun k => (lift (fst T (A ⊗ A)) (snd _ _ ≫ rosO A f g k)).left
  have hφ : ∀ k, φ k ≫ (snd T A).left = (snd T (A ⊗ A)).left ≫ rosatiφ A f g k := fun k => by
    rw [← rosO_left, ← Over.comp_left, ← Over.comp_left, lift_snd]
  have hφc : ∀ c k, (lift (𝟙 T) c).left ≫ φ k = (lift (𝟙 T) (c ≫ rosO A f g k)).left := fun c k => by
    rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
  obtain ⟨a, ha, va⟩ := exists_gen hL (φ' := fun k => φ k ≫ (snd T A).left) (ε' := rosatiε)
    (fun U _ h => by simp only [hφ]) (LB.pullGen L _ _ u (snd T (A ⊗ A)).left) (DVR.pullGen_isGen _ _ _ _ hu _)
  obtain ⟨s, hs, vs⟩ := GlobalTheory.EndRosati.exists_gen_through hL hL' w hw φ rosatiε a ha
  have ev : ∀ (c : T ⟶ A ⊗ A) (y : Sp F) N J, Good L y N → Good L' y J → val s (lift (𝟙 T) c).left y J =
      (∏ k, gw w (lift (𝟙 T) (c ≫ rosO A f g k)).left y (J (ψ (c ≫ rosO A f g k)).left)
        (fun _ => N (c ≫ rosO A f g k).left) ^ rosatiε k) * val u c.left y N := fun c y N J hN hJ => by
    rw [vs _ _ y J N hJ hN, va _ _ y N hN, val_pull hN, ← Over.comp_left, lift_snd]
    refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
    rw [hφc, hψ, ← Over.comp_left, lift_snd]
  have ev' : ∀ (x x' : T ⟶ A) (y : Sp F) J, Good L' y J →
      val (LB.pullGen L' _ _ u' H.left) (lift (𝟙 T) (lift x x')).left y J = val u' (lift (ψ x) (ψ x')).left y J :=
    fun x x' y J hJ => by rw [val_pull hJ, ← hH]; rfl
  have hp : Function.Surjective p.appTop.hom := by
    let β : Y ≅ A ⊗ (A ⊗ T) := β_ _ _ ≪≫ α_ _ _ _
    have e : p = β.hom.left ≫ (snd A (A ⊗ T)).left ≫ (snd A T).left := by
      have : fst T (A ⊗ A) = β.hom ≫ snd A (A ⊗ T) ≫ snd A T := by simp [β, Y]
      exact congrArg (·.left) this
    rw [e]
    refine surj_comp ?_ (surj_comp (surj_snd hG hA _) (surj_snd hG hA _))
    have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget S).map β.hom))
    have : IsIso β.hom.left.appTop := inferInstanceAs (IsIso (β.hom.left.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso β.hom.left.appTop).2
  refine (ev' b b' z J hJ).symm.trans (Eq.trans ?_ (ev _ z N J hN hJ))
  refine gen_unique' hL' (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ _) (hE k)) p
    (lift (𝟙 T) (lift 1 1)).left (by rw [← Over.comp_left, lift_fst]; rfl) hp
    (DVR.pullGen_isGen _ _ _ _ hu' _) hs (fun y I hI => ?_) _ _ z J hJ
  choose M hM using fun χ : Sp F ⟶ A.left => exists_chart hL (χ y)
  have o : ∀ k, lift (1 : T ⟶ A) 1 ≫ rosO A f g k = 1 := fun k => by
    rw [lift_rosO]; fin_cases k <;> simp [MonObj.one_comp]
  refine (ev' _ _ y I hI).trans (Eq.trans ?_ (ev _ y M I hM hI).symm)
  rw [map_one, val_origin u₀' (T := T') hI, val_origin u₀ (T := T) hM]
  simp [o, rosatiε, Fin.prod_univ_succ]

theorem rosV_move : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (Φ : (TF (R := R) F ⊗ D.P.A).left ⟶ D'.P.A.left) (w : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull Φ)) (φ : N.A →* N'.A) (wv : N.A → F), w.IsGen → Φ ≫ D'.P.A.hom = (fst (TF (R := R) F) D.P.A).left ≫ (TF (R := R') F).hom → (∀ x, (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ Φ = (ν'.eA (φ x)).left) → (∀ x, wv x = valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w.s (fun _ => ν'.J (ν'.eA (φ x)).left, fun _ => ν.J (ν.eA x).left)).val) → (∀ y b, φ (actV ν oa y b) = actV ν' oa' y (φ b)) → ∀ (a : O) ρ ρ', RosV ν oa a ρ → RosV ν' oa' a ρ' → ∀ b b', ρ' (φ b) (φ b') * (wv (actV ν oa (star a) b) * wv b' * wv (b * actV ν oa a b')) = ρ b b' * (wv (actV ν oa (star a) b * b') * wv b * wv (actV ν oa a b')) := by
  intro hL R R' _ _ _ _ D D' F _ _ _ _ N N' ν ν' O _ _ oa oa' Φ w φ wv hw hΦ hφ hwv hact a ρ ρ' ⟨u, hu, u₀, hρ⟩
    ⟨u', hu', u₀', hρ'⟩ b b'
  have := oa.hom a
  have := oa.hom (star a)
  let ψ : (TF (R := R) F ⟶ D.P.A) →* (TF (R := R') F ⟶ D'.P.A) :=
    (ν'.eA.toMonoidHom.comp φ).comp ν.eA.symm.toMonoidHom
  have e : ∀ x, ψ (ν.eA x) = ν'.eA (φ x) := fun x => by simp [ψ]
  have ea : ∀ y x, ν.eA (actV ν oa y x) = ν.eA x ≫ oa.act y := fun y x => ν.eA.apply_symm_apply _
  have hf : ∀ y x, ψ (x ≫ oa.act y) = ψ x ≫ oa'.act y := fun y x => by
    obtain ⟨x, rfl⟩ := ν.eA.surjective x
    rw [← ea, e, e, hact]; exact ν'.eA.apply_symm_apply _
  have hψ : ∀ x, (lift (𝟙 (TF (R := R) F)) x).left ≫ Φ = (ψ x).left := fun x => by
    obtain ⟨x, rfl⟩ := ν.eA.surjective x
    rw [e, hφ]
  let z : Sp F := IsLocalRing.closedPoint F
  have hN : Good D.P.L z ν.J := fun q => ν.good q trivial
  have hJ : Good D'.P.L z ν'.J := fun q => ν'.good q trivial
  have H := val_move hL.globalFns _ _ D.P.isAb D'.P.isAb D.P.isLB D'.P.isLB Φ w hw hΦ ψ hψ _ _ _ _ (hf (star a)) (hf a)
    hu u₀ hu' u₀' z ν.J ν'.J hN hJ (ν.eA b) (ν.eA b')
  let W : (TF (R := R) F ⟶ D.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun x =>
    gw w (lift (𝟙 (TF (R := R) F)) x).left z (ν'.J (ψ x).left) (fun _ => ν.J x.left)
  have hW : ∀ x, toStk z (wv x) = (W (ν.eA x)).val := fun x => by
    rw [hwv, ← e]
    have m₁ : Φ ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left z) ∈ D'.P.L.U (ν'.J (ψ (ν.eA x)).left) :=
      (congrArg (fun q : Sp F ⟶ _ => q z ∈ D'.P.L.U (ν'.J (ψ (ν.eA x)).left)) (hψ (ν.eA x))).mpr (hJ _)
    have m₂ : (snd (TF (R := R) F) D.P.A).left ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left z) ∈ D.P.L.U (ν.J (ν.eA x).left) :=
      (congrArg (fun q : TF (R := R) F ⟶ _ => q.left z ∈ D.P.L.U (ν.J (ν.eA x).left))
        (lift_snd (𝟙 (TF (R := R) F)) (ν.eA x))).mpr (hN _)
    exact toStk_valF _ (_ ⊓ _) z ⟨mem_pull.2 m₁, mem_pull.2 m₂⟩ _
  have H' : val (Z := Sp F) u' (lift (ν'.eA (φ b)) (ν'.eA (φ b'))).left z ν'.J =
      (∏ k, W (lift (ν.eA b) (ν.eA b') ≫ rosO _ (oa.act (star a)) (oa.act a) k) ^ rosatiε k) * val (Z := Sp F) u (lift (ν.eA b) (ν.eA b')).left z ν.J := by
    rw [← e, ← e]; exact H
  have v : toStk z (ρ b b') = (val (Z := Sp F) u (lift (ν.eA b) (ν.eA b')).left z ν.J).val := by
    rw [hρ]; exact toStk_valF _ _ z (hN.mem _ _) _
  have v' : toStk z (ρ' (φ b) (φ b')) = (val (Z := Sp F) u' (lift (ν'.eA (φ b)) (ν'.eA (φ b'))).left z ν'.J).val := by
    rw [hρ']; exact toStk_valF _ _ z (hJ.mem _ _) _
  apply (toStk z).injective
  simp only [map_mul, hW, v, v', ea, ← Units.val_mul, H', lift_rosO]
  congr 1
  clear_value W
  apply Additive.ofMul.injective
  simp [rosatiε, Fin.prod_univ_succ, ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.RosMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAVIso_descends_of_rational_threeTorsion : Laws → Laws2 → GlobalTheory.LN.HomExtSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] (B B' : PolAV (Sp R)), RatTors B C 3 → RatTors B' C 3 → ∀ (φ : TF (R := R) C ⊗ B.A ≅ TF (R := R) C ⊗ B'.A) (g : (TF (R := R) C ⟶ B.A) ≃* (TF (R := R) C ⟶ B'.A)), φ.hom ≫ fst _ _ = fst _ _ → (∀ x, lift (𝟙 _) x ≫ φ.hom = lift (𝟙 _) (g x)) → LBIso (B.L.pull (snd (TF (R := R) C) B.A).left) (B'.L.pull (φ.hom ≫ snd (TF (R := R) C) B'.A).left) → ∃ Ψ : B'.A ≅ B.A, IsMonHom Ψ.hom ∧ LBIso B'.L (B.L.pull Ψ.hom.left) ∧ ∀ x, g x ≫ Ψ.hom = x := by
  first | exact @GlobalTheory.polAV_iso_descends_of_ratTors | exact GlobalTheory.polAV_iso_descends_of_ratTors | (intros; apply GlobalTheory.polAV_iso_descends_of_ratTors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsAllPrimePowerLevelsOfSingleObjectStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoints_allPrimePowerLevels_of_single_object : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n : ℕ), n.Prime → Odd n → (∀ j, 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j))) → ∃ o : Full D K, o.ρ = S.A.ρ ∧ ∀ j, o.I.ζ (n ^ j) = S.A.I.ζ (n ^ j) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  first | exact @GlobalTheory.Ex.AllLevels.one_object | exact GlobalTheory.Ex.AllLevels.one_object | (intros; apply GlobalTheory.Ex.AllLevels.one_object <;> assumption)
end

