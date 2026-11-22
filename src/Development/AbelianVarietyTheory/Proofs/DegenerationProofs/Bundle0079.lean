import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0068
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0063
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isLocallyNoetherian [IsNoetherianRing o] : IsLocallyNoetherian M.Z :=
  have := M.lft
  LocallyOfFiniteType.isLocallyNoetherian M.s

def ptOpen (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : Sp Ω ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι M.pt (by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hV))

theorem ptOpen_ι (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : M.ptOpen V hV ≫ V.ι = M.pt :=
  IsOpenImmersion.lift_fac _ _ _

def openPart [IsNoetherianRing o] (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : RatModel o Ω :=
  haveI : Nonempty V.toScheme := ⟨⟨hV.some, hV.some_mem⟩⟩
  haveI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  { Z := V.toScheme
    s := V.ι ≫ M.s
    sep := have := M.sep; inferInstance
    lft := have := M.lft; inferInstance
    qc := have := M.qc; have := M.isLocallyNoetherian; inferInstance
    pt := M.ptOpen V hV
    pt_s := by rw [← Category.assoc, ptOpen_ι, M.pt_s]
    gen := by
      have h : ∀ w : Sp Ω, M.ptOpen V hV w = genericPoint V.toScheme := fun w => by
        apply V.ι.isOpenEmbedding.injective
        rw [genericPoint_eq_of_isOpenImmersion, ← M.pt_apply w, ← M.ptOpen_ι V hV]
        rfl
      exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, h (IsLocalRing.closedPoint Ω)⟩, by
        rintro _ ⟨w, rfl⟩
        exact h w⟩
    onto := fun x => by
      obtain ⟨U, f, hU, rfl⟩ := M.onto x
      obtain ⟨z, hz, hz'⟩ := M.nonempty_inf hU hV
      refine ⟨V.ι ⁻¹ᵁ U, V.ι.app U f, ⟨⟨z, hz'⟩, hz⟩, ?_⟩
      refine (valR_comp _ _ U f).symm.trans ?_
      rw [ptOpen_ι]
      rfl }

theorem isHom_openPart [IsNoetherianRing o] (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) :
    M.IsHom (M.openPart V hV) (AlgHom.id o Ω) V.ι :=
  (M.ptOpen_ι V hV).trans ((Category.id_comp _).symm.trans (congrArg (· ≫ M.pt) (Spec.map_id _).symm))

variable {M}

theorem IsHom.O_eq {N : RatModel o Ω} {j : N.Z ⟶ M.Z} (h : M.IsHom N (AlgHom.id o Ω) j) [IsOpenImmersion j]
    (z : N.Z) : N.O z = M.O (j z) := by
  refine le_antisymm ?_ fun x hx => h.map_mem_O hx
  rintro _ ⟨U, g, hz, rfl⟩
  have hz' : j z ∈ j ''ᵁ U := ⟨z, hz, rfl⟩
  refine ⟨j ''ᵁ U, (j.appIso U).inv g, hz', ?_⟩
  refine (h.valF_app ⟨_, hz'⟩ _).symm.trans ?_
  have e := congrArg (fun φ => φ.hom g) (j.appIso_inv_app U)
  refine (congrArg _ e).trans ?_
  exact N.valF_resG (j.preimage_image_eq U).le ⟨z, hz'⟩ g

variable (M)

structure GenTriv (H : LB M.Z) (d : H.ι → Ω) : Prop where
  ne : ∀ k, d k ≠ 0
  g_eq : ∀ k k', ((H.U k ⊓ H.U k' : M.Z.Opens) : Set M.Z).Nonempty →
    valF M.pt (H.U k ⊓ H.U k') (H.g k k' : Γ(M.Z, H.U k ⊓ H.U k')) = d k' / d k

def HasVal {H : LB M.Z} (d : H.ι → Ω) (σ : H.Sec) (x : Ω) : Prop :=
  ∀ k, (H.U k : Set M.Z).Nonempty → valF M.pt (H.U k) (σ.f k) = x / d k

def ProjChart {Ω' : Type} [Field Ω'] [Algebra o Ω'] (N : RatModel o Ω') (φ : Ω →ₐ[o] Ω') (q : N.Z ⟶ M.Z)
    (W : M.Z.Opens) {J : Type} (t : J → Ω') : Prop :=
  (∀ z', q z' ∈ W → ∃ i, N.Div t i z') ∧ ∀ i, t i ≠ 0 → ∃ U : N.Z.Opens, IsAffineOpen U ∧
    (U : Set N.Z) = {z' | q z' ∈ W ∧ N.Div t i z'} ∧
    N.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => t j / t i)

example : M.GenTriv ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ fun _ => 1 :=
  ⟨fun _ => one_ne_zero, fun _ _ h => (valR_one _ _ (M.top_le_preimage_pt h)).trans (div_one 1).symm⟩

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLinCombIffPullbackMulGenerator
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gs_linSum {Y Z : Scheme.{0}} {R : Type} [CommRing R] (p : Y ⟶ Sp R) {I : Type} [Fintype I] (a : I → R)
    (r : Z ⟶ Y) (z : Z) (W : Y.Opens) (hm : r z ∈ W) (f : I → Γ(Y, W)) :
    gs r z W (∑ i, constFn p W (a i) * f i) = ∑ i, cst (r ≫ p) z (a i) * gs r z W (f i) := by
  have e : ∀ (b : I → Γ(Y, W)), gs r z _ (∑ i, b i) = ∑ i, gs r z _ (b i) := fun b => by
    simp only [gs_eq r z _ hm, map_sum]
  rw [e]
  exact Finset.sum_congr rfl fun i _ => (gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_constFn p _ r z hm _) rfl)

theorem isLin_iff_of_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ (I : Type) [Fintype I] (b : I → LB.Sec (LB.LinComb L ψ ε)) (φ : I → (Φ.H 1).Sec) (b₀ : LB.Sec (LB.LinComb L ψ ε)) (φ₀ : (Φ.H 1).Sec) (a : I → k), (∀ i, UFib.Red Φ c t (b i) (φ i)) → UFib.Red Φ c t b₀ φ₀ → (IsLin Φ.E.B.hom b a b₀ ↔ IsLin Φ.G.hom φ a φ₀) := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t _ I _ b φ b₀ φ₀ a hb hb₀
  have pick : ∀ (y : Φ.G.left) (l : Φ.N₀.ι), y ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l →
      ∃ J, Good L y J ∧ J (𝟙 _ ≫ Φ.D.q.left ≫ π) = c.idx l := fun y l hy => by
    obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : PUnit => 𝟙 _ ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
      (fun _ _ _ => rfl) (fun _ => c.le l hy)
    exact ⟨J, hJ, e PUnit.unit⟩
  have hw : (𝟙 _ ≫ Φ.D.q.left) ≫ Φ.E.B.hom = 𝟙 _ ≫ Φ.G.hom := by
    rw [Category.assoc, Over.w]
  constructor
  · intro h l
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := pick y l hy
    refine (hb₀ _ (𝟙 _) y J hJ l hy e).trans (Eq.trans ?_ (gs_linSum Φ.G.hom a (𝟙 _) y _ hy _).symm)
    have m := hJ.mem ψ (𝟙 _ ≫ Φ.D.q.left)
    have e₁ : sval b₀ (𝟙 _ ≫ Φ.D.q.left) y J =
        ∑ i, cst (𝟙 _ ≫ Φ.G.hom) y (a i) * sval (b i) (𝟙 _ ≫ Φ.D.q.left) y J := by
      rw [← hw]
      exact (congrArg (gs _ y _) (h _)).trans (gs_linSum Φ.E.B.hom a _ y _ m _)
    rw [e₁, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (mul_assoc _ _ _).trans (congrArg _ (hb i _ (𝟙 _) y J hJ l hy e).symm)
  · intro h j
    have := Φ.D.q_flat
    have := Φ.D.q_surjective
    apply GlobalTheory.FunDescent.app_injective Φ.D.q.left
    refine fn_ext fun y hy => ?_
    refine (gs_pull (𝟙 _) Φ.D.q.left y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) Φ.D.q.left y _ hy _).symm)
    refine Eq.trans ?_ (gs_linSum Φ.E.B.hom a (𝟙 _ ≫ Φ.D.q.left) y _ hy _).symm
    obtain ⟨l, hl⟩ := exists_chart Φ.isLB (Φ.D.q.left y)
    obtain ⟨J, hJ, e⟩ := pick y l hl
    have m := hJ.mem ψ (𝟙 _ ≫ Φ.D.q.left)
    have e₁ : sval b₀ (𝟙 _ ≫ Φ.D.q.left) y J =
        ∑ i, cst (𝟙 _ ≫ Φ.G.hom) y (a i) * sval (b i) (𝟙 _ ≫ Φ.D.q.left) y J := by
      refine (Units.mul_left_inj (val t (𝟙 _) y J)).1 ?_
      refine (hb₀ _ (𝟙 _) y J hJ l hl e).symm.trans ((congrArg (gs _ y _) (h l)).trans
        ((gs_linSum Φ.G.hom a (𝟙 _) y _ hl _).trans ?_))
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (congrArg _ (hb i _ (𝟙 _) y J hJ l hl e)).trans (mul_assoc _ _ _).symm
    refine (sec_trans b₀ (𝟙 _ ≫ Φ.D.q.left) y (j := j) hy m).trans ((congrArg _ e₁).trans ?_)
    rw [Finset.mul_sum, hw]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (mul_left_comm _ _ _).trans (congrArg _ (sec_trans (b i) (𝟙 _ ≫ Φ.D.q.left) y (j := j) hy m).symm)

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PointDescendsToValuationRingStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_descends_to_valuationRing' : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (W C : Type) [CommRing W] [IsLocalRing W] [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C), IsLocalHom α → Function.Injective β → β.comp α = ga.comp (algebraMap V (FractionRing V)) → ∀ (X : Scheme.{0}) (y : Sp W ⟶ X) (x : Sp (FractionRing V) ⟶ X), spMap β ≫ y = spMap ga ≫ x → ∃ h : Sp V ⟶ X, spMap α ≫ h = y ∧ jK V ≫ h = x := by
  first | exact @GlobalTheory.point_descends_to_valuationRing | exact GlobalTheory.point_descends_to_valuationRing | (intros; apply GlobalTheory.point_descends_to_valuationRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProjZeroPullbackNeZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

namespace GlobalTheory.ThetaInvPart

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem diag_eq [IsDomain o] {Q : Type} [AddCommGroup Q] [Fintype Q] (π : S.Gam →+ Q) (i₀ : S.J)
    (hc : Fintype.card S.J = Fintype.card Q)
    (hfix : ∀ a, π a = 0 → ∀ l, S.ρ a l i₀ = if l = i₀ then 1 else 0)
    (horb : ∀ i, ∃ a, ∃ e : ℕ, ∀ l, S.ρ a l i₀ = if l = i then S.ζ ^ e else 0) (a : S.Gam) :
    S.ρ a i₀ i₀ = if π a = 0 then 1 else 0 := by
  have hζ : S.ζ ≠ 0 := S.prim.ne_zero (pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega)
    (by have := S.N_ge; omega)))
  choose c e hce using horb
  have key : ∀ a b, π a = π b → ∃ k : ℕ, ∀ l, S.ρ b l i₀ = S.ζ ^ k * S.ρ a l i₀ := fun a b h => by
    obtain ⟨k, hk⟩ := S.ρ_mul b (a - b)
    refine ⟨k, fun l => ?_⟩
    have := congrFun (congrFun hk l) i₀
    rw [Matrix.mul_apply, add_sub_cancel, Matrix.smul_apply, smul_eq_mul] at this
    simpa [hfix (a - b) (by rw [map_sub, h, sub_self])] using this
  have inj : Function.Injective fun i => π (c i) := fun i j h => by
    obtain ⟨k, hk⟩ := key _ _ h
    by_contra hij
    have := hk j
    rw [hce, hce, if_pos rfl, if_neg (Ne.symm hij), mul_zero] at this
    exact pow_ne_zero _ hζ this
  have surj := ((Fintype.bijective_iff_injective_and_card _).2 ⟨inj, hc⟩).2
  have zero : ∀ a i, π (c i) = π a → i ≠ i₀ → S.ρ a i₀ i₀ = 0 := fun a i h hi => by
    obtain ⟨k, hk⟩ := key _ _ h
    rw [hk, hce, if_neg (Ne.symm hi), mul_zero]
  split_ifs with ha
  · rw [hfix a ha, if_pos rfl]
  · obtain ⟨i, hi⟩ := surj (π a)
    refine zero a i hi fun h => ?_
    obtain ⟨j, hj⟩ := surj (π 0)
    by_cases h' : j = i₀
    · exact ha (by rw [← hi, h, ← h', hj, map_zero])
    · have := zero 0 j hj h'
      rw [hfix 0 (map_zero π), if_pos rfl] at this
      exact one_ne_zero this

theorem rho_fix (hG : GlobalFnsSt) (hi : Function.Injective (algebraMap o Ω)) (ρ : S.Real) (a : S.Gam)
    (ha : (ρ.n ^ ρ.k) • S.r • a = 0) (l : S.J) : S.ρ a l ρ.i₀ = if l = ρ.i₀ then 1 else 0 := by
  have := ρ.P.isAb.comm
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp : ∀ (n : ℕ) b, ρ.pt (n • b) = ρ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hm : ρ.pt (S.r • a) ^ (ρ.n ^ ρ.k) = 1 := by rw [← hp, ha, h0]
  have hN : ρ.pt (S.r • a) ^ S.N = 1 :=
    (congrArg _ (ρ.N_eq.trans (sq _))).trans (by rw [pow_mul, hm, one_pow])
  obtain ⟨ν, hν⟩ := exists_gen_negLB hG _ ρ.P 1 (baseOver (Sp S.R))
  have hact := ThetaCoord.isActOf_self hG ρ.P.isAb ρ.P.isLB (q := S.N) (b := 1)
    (by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow) hν ρ.α_gen ρ.s_zero hm hN (ρ.U_sym a)
  have h₁ := ρ.U_act a ρ.i₀ _ hact
  have h₂ : ∀ j, (ρ.s ρ.i₀).f j = ∑ l, liftFun ρ.P.A _ (fn (algebraMap o S.R (if l = ρ.i₀ then 1 else 0))) *
      (ρ.s l).f j := fun j => by
    rw [Finset.sum_eq_single ρ.i₀ (fun b _ hb => by simp [hb, liftFun]) (by simp)]
    simp [liftFun]
  have h₃ := congrFun ((ρ.s_basis (ρ.s ρ.i₀)).unique h₁ h₂) l
  have h₄ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv).1 h₃
  exact hi (congrArg Subtype.val h₄)

end GlobalTheory.ThetaInvPart

namespace GlobalTheory

open ThetaInvPart

theorem proj_zero_pullback_ne_zero : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (S : ThetaSys o Ω) (ρ : S.Real) (k : Type) [Field k] (y : o →+* k) (T : AddSubgroup S.Gam), S.IsoFree T →
    ∃ j, y (S.proj T 0 j ρ.i₀) ≠ 0 := by
  intro hL o Ω _ _ _ hA S ρ k _ y T _
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero (ρ.n ^ ρ.k) := ⟨pow_ne_zero _ ρ.n_prime.ne_zero⟩
  have : IsDomain o := hA.inj.isDomain _
  have hd : ρ.n ^ ρ.k ∣ S.r * S.N := by
    rw [ρ.N_eq]; exact Dvd.dvd.mul_left (dvd_pow_self _ two_ne_zero) _
  let π : S.Gam →+ (Fin S.g ⊕ Fin S.g → ZMod (ρ.n ^ ρ.k)) :=
    (ZMod.castHom hd (ZMod (ρ.n ^ ρ.k))).toAddMonoidHom.compLeft _
  have hdiag := diag_eq π ρ.i₀ (by
      rw [ρ.card, ρ.N_eq, ← pow_mul]
      simp [two_mul])
    (fun a ha => rho_fix hL.1.globalFns hA.inj ρ a (funext fun i => by
      have h : ZMod.castHom hd (ZMod (ρ.n ^ ρ.k)) (a i) = 0 := congrFun ha i
      rw [← ZMod.natCast_zmod_val (a i), map_natCast, ZMod.natCast_eq_zero_iff] at h
      obtain ⟨c, hc⟩ := h
      rw [Pi.smul_apply, Pi.smul_apply, ← ZMod.natCast_zmod_val (a i), hc, nsmul_eq_mul, nsmul_eq_mul,
        ← Nat.cast_mul, ← Nat.cast_mul, Pi.zero_apply, ZMod.natCast_eq_zero_iff]
      exact ⟨c, by rw [ρ.N_eq]; ring⟩)) ρ.orbit
  have hu : ∀ n : ℕ, n ∣ Nat.card S.Gam → IsUnit (n : o) := fun n hn => by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast hn) ?_
    rw [Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  refine ⟨ρ.i₀, (IsUnit.map y ?_).ne_zero⟩
  have := Fintype.ofFinite T
  have hT := AddSubgroup.card_addSubgroup_dvd_card T
  have hK := (AddSubgroup.card_addSubgroup_dvd_card (π.comp T.subtype).ker).trans hT
  have hs : ∑ t : T, S.ρ t ρ.i₀ ρ.i₀ = (Nat.card (π.comp T.subtype).ker : o) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hdiag]
    by_cases h : π t = 0 <;> simp [AddMonoidHom.mem_ker, h]
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp only [AddMonoidHom.zero_apply, neg_zero, ZMod.val_zero, pow_zero, one_smul]
  rw [hs]
  exact (hu _ hT).ringInverse.mul (hu _ hK)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenDescendBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiEven_descend_baseChange : GlobalFnsSt → ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D'.PsiEven → D.PsiEven := by
  first | exact @GlobalTheory.PsiRing.psiEven_descend | exact GlobalTheory.PsiRing.psiEven_descend | (intros; apply GlobalTheory.PsiRing.psiEven_descend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenTauBimultDescendOfInjectiveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiEven_tauBimult_descend_of_injective : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre R') (_ : IsPullDeg φ D D'), (D'.PsiEven → D.PsiEven) ∧ (D'.TauBimult → D.TauBimult) := by
  first | exact @GlobalTheory.psiEven_tauBimult_of_isPullDeg_injective | exact GlobalTheory.psiEven_tauBimult_of_isPullDeg_injective | (intros; apply GlobalTheory.psiEven_tauBimult_of_isPullDeg_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelationDescendsFieldExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_relation_descends_field_extension : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oa : D.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oa.onB.act a).left) → ∀ w : O, TraceFormTwistIso D' oa' w → TraceFormTwistIso D oa w := by
  first | exact @GlobalTheory.psi_relation_descend_field | exact GlobalTheory.psi_relation_descend_field | (intros; apply GlobalTheory.psi_relation_descend_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiScalarEqExpansionCoefRatioStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiScalar_eq_expansionCoef_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), PsiScal D ga a → PsiRel D (𝟙_ _) f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ (χ : D.X) (q p : R), Mult D th (f 0) q → Coef D χ (ga χ) th (f χ) p → algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p := by
  first | exact @GlobalTheory.psiScal_eq_ratio | exact GlobalTheory.psiScal_eq_ratio | (intros; apply GlobalTheory.psiScal_eq_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiScalarMemOfPsiMemIdeal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem scalar_mem_of_psiIn : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → ∀ (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), PsiScal D ga a → ∀ (x : D'.X) (J' : Ideal V), D'.PsiIn x J' → ∀ p q : R, algebraMap R (FractionRing R) q * (a (xe x)).val = algebraMap R (FractionRing R) p → ∃ m ∈ J', φ p = φ q * m := by
  intro R V _ _ _ _ _ φ D D' β v xe _ hv hc gam hgam hψ ga a hS x J' hJ' p q hpq
  obtain ⟨ga', a', hS'⟩ := exists_psiScal V D'
  obtain ⟨m₀, hm₀, em₀⟩ := (PsiScalIn.main_local D' ga' a' hS' x J').1 hJ'
  obtain ⟨t, ht, Ht⟩ := CubTransport.exists_pmaps ((isGen_iff v).1 hv) D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => (D'.c x).left) (φ := fun _ => (D.c (xe x)).left) (ε := fun _ => -1) (spMap φ) (fun _ => hc x)
    (ga (xe x)) (hS (xe x)).1
  obtain ⟨c, hcu⟩ := exists_unit_val_eq_mul D'.P.isLB (hS' x).1 ht
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing V))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  choose I hI using fun χ : (TK V).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  choose I' hI' using fun χ : (TK V).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ z)
  have gI : Good D.P.L (Z := (TK V).left) z I := hI
  have gI' : Good D'.P.L (Z := (TK V).left) z I' := hI'
  have hx : D'.xK x ≫ β = gam ≫ D.xK (xe x) := by
    change (jK V ≫ (D'.c x).left) ≫ β = gam ≫ jK R ≫ (D.c (xe x)).left
    rw [Category.assoc, hc x, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (D.c (xe x)).left) hgam.symm
  have e₁ := CubTransport.val_pmaps (fun _ => hx) (hψ x) (𝟙 _) gI gI'
  have e₂ := CubTransport.val_pmaps (fun _ => hc x) Ht (jK V) gI gI'
  have e₃ := (hS (xe x)).2 (Over.mk (gam ≫ jK R)) (Over.homMk gam rfl) z I gI
  have e₄ := (hS' x).2 (TK V) (𝟙 _) z I' gI'
  have e₅ := hcu _ (jK V) z I' gI'
  rw [Category.id_comp, Fintype.prod_unique, Category.id_comp] at e₁
  rw [Fintype.prod_unique, ← hgam] at e₂
  obtain ⟨Ω, f₁, f₂⟩ : ∃ Ω : ((Spec (CommRingCat.of (FractionRing V))).presheaf.stalk z)ˣ,
      val (Z := Spec (CommRingCat.of (FractionRing V))) (D.psi (xe x)) gam z I = Ω * val (Z := Spec (CommRingCat.of (FractionRing V))) (D'.psi x) (𝟙 _) z I' ∧
        val (Z := Spec (CommRingCat.of (FractionRing V))) (ga (xe x)) (gam ≫ jK R) z I = Ω * val (Z := Spec (CommRingCat.of (FractionRing V))) t (jK V) z I' := ⟨_, e₁, e₂⟩
  have f₃ : (val (Z := Spec (CommRingCat.of (FractionRing V))) (D.psi (xe x)) gam z I).val =
      gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (a (xe x)).val) * (val (Z := Spec (CommRingCat.of (FractionRing V))) (ga (xe x)) (gam ≫ jK R) z I).val := e₃
  have f₄ : (val (Z := Spec (CommRingCat.of (FractionRing V))) (D'.psi x) (𝟙 _) z I').val =
      PsiScalIn.sig z (a' x).val * (val (Z := Spec (CommRingCat.of (FractionRing V))) (ga' x) (jK V) z I').val :=
    e₄.trans (congrArg₂ (· * ·) (PsiScalIn.gs_scal_id z _) rfl)
  let u : V := (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom c.val
  have hu : gs (jK V) z ⊤ c.val = PsiScalIn.sig z (algebraMap V _ u) := by
    refine Eq.trans (congrArg (gs (jK V) z ⊤) ?_) (PsiScalIn.gs_toOpen z ⊤ trivial u)
    simp [u, DegPre.toOpen]
  have key : gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (a (xe x)).val) = PsiScalIn.sig z (algebraMap V _ (m₀ * u)) := by
    rw [f₁, f₂, Units.val_mul, Units.val_mul, f₄, mul_left_comm (gs _ _ _ _), Units.mul_right_inj] at f₃
    have f₅ := f₃.symm.trans (congrArg (PsiScalIn.sig z (a' x).val * ·) (e₅.trans (congrArg (· * _) hu)))
    rw [← _root_.mul_assoc, Units.mul_left_inj] at f₅
    rw [map_mul, map_mul, em₀]
    exact f₅
  have hs : ∀ r : R, gs (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (scal gam (algebraMap R (FractionRing R) r)) =
      PsiScalIn.sig z (algebraMap V _ (φ r)) := fun r => by
    have k : ∀ {A : Type} [CommRing A] (w : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of A)) (s : A),
        gs (𝟙 _) z ⊤ (scal w s) = cst w z s := fun w s =>
      (gs_pull (𝟙 _) w z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
    refine (congrArg _ (PsiInt.scal_jK gam r).symm).trans ((k _ r).trans ?_)
    refine (congrArg (fun w => cst w z r) hgam).trans ((cst_comp (jK V) φ z r).trans ?_)
    refine Eq.trans ?_ (PsiScalIn.gs_toOpen z ⊤ trivial (φ r))
    exact (gs_res (jK V) z (U := ⊤) (V := ⊤) le_top trivial _).symm
  refine ⟨m₀ * u, J'.mul_mem_right u hm₀, IsFractionRing.injective V (FractionRing V) ((PsiScalIn.sig z).injective ?_)⟩
  rw [map_mul (algebraMap V _) (φ q), map_mul (PsiScalIn.sig z), ← hs, ← hs, ← key, ← hpq, ← gs_mul _ z ⊤ trivial]
  unfold scal
  rw [map_mul, map_mul]

end GlobalTheory.PsiRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidificationComparisonUniformisationStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidification_comparison_uniformisation : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I' ≠ ⊤ → I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), RigCmp φ D D' C.β C.v := by
  first | exact @GlobalTheory.rigCmp_of_cmp | exact GlobalTheory.rigCmp_of_cmp | (intros; apply GlobalTheory.rigCmp_of_cmp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableOfPotentialSemiAbelianModelStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_of_potential_semiAbelian_model : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G)) → SemistableReductionZero ∧ SemistableCompleteSplit := by
  first | exact @GlobalTheory.SS.semistable_of_potModel_semiAbelian | exact GlobalTheory.SS.semistable_of_potModel_semiAbelian | (intros; apply GlobalTheory.SS.semistable_of_potModel_semiAbelian <;> assumption)
end

