import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonomialMatricesProjectiveRep
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

namespace GlobalTheory.ThetaReal

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.ThetaReal.exists_monomial_matrices : ∀ (o A M : Type) [CommRing o] [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] (f : o →+* A), Function.Injective f → ∀ (g m r N : ℕ), N = m ^ 2 → 1 ≤ m → 1 ≤ r → ∀ (ζ : o) (q : ℕ), 1 ≤ q → ζ ^ q = 1 → ∀ (_ : Module.Basis (Fin (N ^ g)) A M) (u : (Fin g ⊕ Fin g → ZMod (r * N)) → M →ₗ[A] M) (s₀ : M), (∀ a, r • a = 0 → ∀ v, u a v = v) → (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = f (ζ ^ e) • u (a + b) v) → (∀ a b, r • _root_.GlobalTheory.ZH.eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) → (∀ a, (r * m) • a = 0 → u a s₀ = s₀) → Submodule.span A (Set.range fun a => u a s₀) = ⊤ → ∃ (J : Type) (_ : Fintype J) (ρ : (Fin g ⊕ Fin g → ZMod (r * N)) → Matrix J J o) (s : Module.Basis J A M) (i₀ : J), Fintype.card J = N ^ g ∧ s i₀ = s₀ ∧ (∀ a, r • a = 0 → ρ a = 1) ∧ (∀ a b, ∃ k : ℕ, ρ a * ρ b = ζ ^ k • ρ (a + b)) ∧ (∀ a b, r • _root_.GlobalTheory.ZH.eStd g _ a b = 0 → ρ a * ρ b = ρ (a + b)) ∧ (∀ a i, u a (s i) = ∑ l, f (ρ a l i) • s l) ∧ ∀ i, ∃ a, ∃ e : ℕ, ∀ l, ρ a l i₀ = if l = i then ζ ^ e else 0 := by
  intro o A M _ _ _ _ _ f hf g m r N hN hm hr ζ q hq hζ b u s₀ hker hmul hcomm hfix hspan
  subst hN
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩

  let rep : (Fin g ⊕ Fin g → Fin m) → (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) :=
    fun j k => ((j k : ℕ) : ZMod (r * m ^ 2))
  let cls : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → (Fin g ⊕ Fin g → Fin m) :=
    fun a k => ⟨(a k).val % m, Nat.mod_lt _ hm⟩
  haveI : NeZero (r * m ^ 2) := ⟨(Nat.mul_pos (by omega) (pow_pos (by omega) 2)).ne'⟩
  have hzero : ((r : ZMod (r * m ^ 2)) * (m : ZMod (r * m ^ 2)) ^ 2) = 0 := by
    exact_mod_cast ZMod.natCast_self (r * m ^ 2)
  have hcls : ∀ a, (r * m) • (a - rep (cls a)) = 0 := fun a => by
    funext k
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, nsmul_eq_mul, rep, cls]
    have hx : a k - (((a k).val % m : ℕ) : ZMod (r * m ^ 2)) = (((m * ((a k).val / m) : ℕ) : ZMod (r * m ^ 2))) := by
      rw [sub_eq_iff_eq_add, ← Nat.cast_add, Nat.div_add_mod, ZMod.natCast_zmod_val]
    rw [hx]
    push_cast
    linear_combination (((a k).val / m : ℕ) : ZMod (r * m ^ 2)) * hzero
  have hrep : ∀ j, cls (rep j) = j := fun j => by
    funext k
    apply Fin.ext
    have hlt : (j k : ℕ) < r * m ^ 2 :=
      lt_of_lt_of_le (j k).isLt (by nlinarith)
    simp only [rep, cls, ZMod.val_natCast_of_lt hlt, Nat.mod_eq_of_lt (j k).isLt]
  have hrep0 : rep (cls 0) = 0 := by
    funext k
    simp [rep, cls]
  let s : (Fin g ⊕ Fin g → Fin m) → M := fun j => u (rep j) s₀
  have hA : ∀ a, ∃ c : ℕ, u a s₀ = f (ζ ^ c) • s (cls a) := fun a => by
    obtain ⟨e, he⟩ := hmul (rep (cls a)) (a - rep (cls a))
    have h1 := he s₀
    rw [hfix _ (hcls a), add_sub_cancel] at h1
    refine ⟨e * q, ?_⟩
    show u a s₀ = f (ζ ^ (e * q)) • u (rep (cls a)) s₀
    rw [h1, smul_smul, ← map_mul, ← pow_add]
    have : e * q + e = e * (q + 1) := by ring
    rw [this, pow_mul', hζ, one_pow, map_one, one_smul]
  have hB : ∀ a j, ∃ c : ℕ, u a (s j) = f (ζ ^ c) • s (cls (a + rep j)) := fun a j => by
    obtain ⟨e, he⟩ := hmul a (rep j)
    obtain ⟨c, hc⟩ := hA (a + rep j)
    refine ⟨e + c, ?_⟩
    show u a (u (rep j) s₀) = _
    rw [he, hc, smul_smul, ← map_mul, ← pow_add]
  have hcard : Fintype.card (Fin g ⊕ Fin g → Fin m) = (m ^ 2) ^ g := by
    simp only [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin]
    ring
  have hspan' : ⊤ ≤ Submodule.span A (Set.range s) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := hA a
    show u a s₀ ∈ Submodule.span A (Set.range s)
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨cls a, rfl⟩)
  let sB : Module.Basis (Fin g ⊕ Fin g → Fin m) A M := basisOfTopLeSpanOfCardEqFinrank s hspan'
    (by rw [hcard, Module.finrank_eq_card_basis b, Fintype.card_fin])
  have hsB : ⇑sB = s := coe_basisOfTopLeSpanOfCardEqFinrank s hspan' _
  choose c hc using hB
  let ρ : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → Matrix (Fin g ⊕ Fin g → Fin m) (Fin g ⊕ Fin g → Fin m) o :=
    fun a => Matrix.of fun l i => if l = cls (a + rep i) then ζ ^ c a i else 0
  have hsum : ∀ a i, u a (sB i) = ∑ l, f (ρ a l i) • sB l := fun a i => by
    rw [hsB, hc a i]
    simp [ρ, apply_ite f, ite_smul]
  have hmat : ∀ a, LinearMap.toMatrix sB sB (u a) = (ρ a).map f := fun a => by
    ext l i
    rw [LinearMap.toMatrix_apply, hsum a i, Module.Basis.repr_sum_self, Matrix.map_apply]
  have hinj : Function.Injective (fun P : Matrix (Fin g ⊕ Fin g → Fin m) (Fin g ⊕ Fin g → Fin m) o => P.map f) :=
    Matrix.map_injective hf
  refine ⟨Fin g ⊕ Fin g → Fin m, inferInstance, ρ, sB, cls 0, hcard, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsB]
    show u (rep (cls 0)) s₀ = s₀
    rw [hrep0]
    exact hker 0 (smul_zero r) s₀
  · intro a ha
    have hid : u a = LinearMap.id := LinearMap.ext (hker a ha)
    apply hinj
    dsimp only
    rw [← hmat, hid, LinearMap.toMatrix_id]
    convert (Matrix.map_one f (map_zero f) (map_one f)).symm
    all_goals first
      | rfl
      | exact Subsingleton.elim _ _
      | (funext x y; exact Subsingleton.elim _ _)
  · intro a a'
    obtain ⟨e, he⟩ := hmul a a'
    refine ⟨e, hinj ?_⟩
    have hcomp : u a ∘ₗ u a' = f (ζ ^ e) • u (a + a') := LinearMap.ext he
    dsimp only
    rw [Matrix.map_mul, ← hmat, ← hmat, ← LinearMap.toMatrix_comp, hcomp, map_smul, hmat]
    ext l i
    simp [Matrix.map_apply, Matrix.smul_apply]
  · intro a a' ha
    apply hinj
    have hcomp : u a ∘ₗ u a' = u (a + a') := LinearMap.ext (hcomm a a' ha)
    dsimp only
    rw [Matrix.map_mul, ← hmat, ← hmat, ← LinearMap.toMatrix_comp, hcomp, hmat]
  · exact hsum
  · intro i
    refine ⟨rep i, c (rep i) (cls 0), fun l => ?_⟩
    simp only [ρ, Matrix.of_apply]
    rw [hrep0, add_zero, hrep]
    split_ifs <;> rfl

end GlobalTheory.ThetaReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOrderActionDescentFieldExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ArcPull PsiEvenPull

theorem exists_oAct_of_field_extension : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oB : D.P.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oB.act a).left) → ∃ oa : D.OAct O, oa.onB = oB := by
  intro hG K₀ K _ _ i D D' hD O _ _ _ _ oB oa' hx ho
  have gp := pull_grp hD
  have hφ : Function.Injective i := i.injective
  have := FieldBaseChange.flat_spMap i
  have := FieldBaseChange.surjective_spMap i
  have : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
  have cl : ∀ (a : O) y, D.c (a • y) = D.c y ≫ oB.act a := fun a y => by
    obtain ⟨y, rfl⟩ := hD.xe.surjective y
    refine Over.OverMorphism.ext ((cancel_epi (spMap i)).1 ?_)
    have e₁ := hD.c_pr (a • y)
    have e₂ := hD.c_pr y
    rw [oa'.c_lin, Over.comp_left, Category.assoc, hx] at e₁
    refine e₁.symm.trans ((congrArg (_ ≫ ·) (ho a)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans (Category.assoc _ _ _))
  refine ⟨⟨oB, cl, fun a u hu u₀ y y' => ?_⟩, rfl⟩
  obtain ⟨y, rfl⟩ := hD.xe.surjective y
  obtain ⟨y', rfl⟩ := hD.xe.surjective y'
  refine corr_of_val_field_extension _ _ (fracMap hφ) _ _ D.P.isLB _ _ _ _ _ _ _ _ fun z J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
  have := oa'.onB.hom a
  have := oa'.onB.hom (star a)
  have := oB.hom a
  have := oB.hom (star a)
  obtain ⟨u', hu', h₀⟩ := exists_ros hG D'.P.isAb D'.P.isLB _ _ (oa'.onB.rosati a)
  have sq := fracMap_sq hφ
  have hh : (TK K).hom ≫ spMap i = genMap hφ ≫ (TK K₀).hom := (Category.id_comp _).symm.trans sq
  have e := val_corr hJ' (oa'.tau_bal a u' hu' h₀ y y') (𝟙 (TK K).left)
  have v := ros_val hG gp D'.P.isAb D.P.isLB D'.P.isLB hD.w_gen (ho a) (ho (star a)) ⟨hu, u₀⟩ ⟨hu', h₀⟩
    (cP D' (TK K) y) (cP D' (TK K) y') (genMap hφ ≫ D.pt2 (hD.xe y) (hD.xe y'))
    ((cPoint_proj hD _ hh y).trans (by
      rw [Category.assoc, DegPre.pt2, ← Over.comp_left, lift_fst]; rfl))
    ((cPoint_proj hD _ hh y').trans (by
      rw [Category.assoc, DegPre.pt2, ← Over.comp_left, lift_snd]; rfl)) hJ hJ'
  have cs : ∀ (a : O) y, cP D' (TK K) y ≫ oa'.onB.act a = cP D' (TK K) (a • y) := fun a y => by
    rw [cP, cP, oa'.c_lin, Category.assoc]
  rw [cs, cs, ← cPoint_add, ← cPoint_add] at v
  rw [val_mul hJ', val_pull hJ'] at e
  erw [Category.id_comp] at e
  beta_reduce at e
  show val _ (genMap hφ) z J = val _ (genMap hφ) z J
  rw [val_mul hJ, val_pull hJ, v]
  beta_reduce
  rw [← hx, ← hx, tau_val hD _ _ sq hJ hJ', tau_val hD _ _ sq hJ hJ']
  simp only [Category.id_comp]
  have e' := congrArg Additive.ofMul e
  apply Additive.ofMul.injective
  have c₀ : ∀ x, (cP D' (TK K) x).left = D'.xK x := fun _ => rfl
  have c₁ : val₂ u' z J' (cP D' (TK K) y) (cP D' (TK K) y') = val u' (D'.pt2 y y') z J' := rfl
  simp only [ofMul_mul, ofMul_inv, c₀, c₁] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrimitiveScaling
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrimScale

open TopologicalSpace GlobalTheory.HolHom

theorem chart_one_le {X : Scheme.{0}} (L : LB X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun _ hy => Set.mem_iInter.1 hy 0

theorem exists_section_firstPower_restrict {X : Scheme.{0}} {L : LB X} (s : L.Sec) : ∃ t : H0 L 1, ∀ j,
    t.f j = (X.presheaf.map (homOfLE (chart_one_le L j)).op).hom (s.f (j 0)) := by
  have le := chart_one_le L
  refine ⟨⟨fun j => (X.presheaf.map (homOfLE (le j)).op).hom (s.f (j 0)),
    fun (i j : Fin 1 → L.ι) => fn_ext fun y hy => ?_⟩, fun _ => rfl⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.1 _)).trans
    ((SecPullIso.gs_sec_trans s (𝟙 X) y (le i hy.1) (le j hy.2)).trans (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val ?_))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.2 _))))))
  refine (gm_linComb L _ _ (𝟙 X) y i j hy.1 hy.2).trans ?_
  simp

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valR x U (a * b) = valR x U a * valR x U b := by
  simp only [valR_eq _ _ h, map_mul]

theorem valR_const {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (p : X ⟶ Sp A) (h : x ≫ p = 𝟙 _) (a : A) :
    valR x ⊤ (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = a := by
  refine (valR_comp x p ⊤ _).symm.trans ?_
  rw [h, valR, dif_pos (show ⊤ ≤ 𝟙 (Sp A) ⁻¹ᵁ ⊤ from le_top)]
  have : Scheme.Hom.appLE (𝟙 (Sp A)) ⊤ ⊤ le_top = 𝟙 _ := (Category.id_comp _).trans ((Sp A).presheaf.map_id _)
  rw [this]
  exact Iso.inv_hom_id_apply _ _

theorem exists_primitive_scaling : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G → ∀ (M : LB G.left), M.IsLB → ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (ψ : pullback G.hom (jK V) ⟶ Y) (w : LB.Iso (M.pull (pullback.fst G.hom (jK V))) (L.pull ψ)), w.IsGen → ∀ θ : LB.Sec L, (∃ z, ψ z ∈ nonzeroLocus θ) → ∃ (ϑ : H0 M 1) (c : FractionRing V), c ≠ 0 ∧ (∃ z ∈ nonzeroLocus ϑ, G.hom z = IsLocalRing.closedPoint V) ∧ ∀ x : Sp (FractionRing V) ⟶ pullback G.hom (jK V), x ≫ pullback.snd G.hom (jK V) = 𝟙 _ → ∀ (i : M.ι) (k : L.ι), ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ M.U i → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U k → valR x _ (w.s (fun _ => k, fun _ => i)).val * valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) = c * valR (x ≫ ψ) _ (θ.f k) := by
  intro V _ _ _ G _ hG M hM Y L hL ψ w hw θ hθ
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hK := IsPullback.of_hasPullback G.hom (jK V)
  have hs := IsPullback.of_hasPullback G.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  obtain ⟨r, hr⟩ := SecPullIso.exists_pull ψ L (M.pull (pullback.fst G.hom (jK V))) w hL (LB.isLB_linComb hM _ _) hw θ
  obtain ⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hs hϖ hM r (by
    obtain ⟨x, hx⟩ := hθ
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hx
    obtain ⟨a, ha⟩ := exists_chart (L := M.pull (pullback.fst G.hom (jK V))) (LB.isLB_linComb hM _ _) x
    have hk' := Y.basicOpen_le _ hk
    have u := (SecPullIso.isUnit_gs_iff ψ x hk' _).2 hk
    rw [hr x k a hk' ha] at u
    have u' := (SecPullIso.isUnit_gs_iff (𝟙 _) x ha _).1 (isUnit_of_mul_isUnit_right u)
    exact ⟨a, fun h => by rw [h, Scheme.basicOpen_zero] at u'; exact u'⟩)
  have h0 : algebraMap V (FractionRing V) ϖ ^ n ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hϖ.ne_zero)
  obtain ⟨ϑ, hϑ⟩ := exists_section_firstPower_restrict σ
  refine ⟨ϑ, _, h0, ⟨x₀, Opens.mem_iSup.2 ⟨fun _ => b, ?_⟩, hx₀⟩, fun x hx i k hi hk => ?_⟩
  · refine (congrArg G.left.basicOpen (hϑ fun _ => b)).ge ?_
    exact (Scheme.basicOpen_res _ _ _).ge ⟨Set.mem_iInter.2 fun _ => G.left.basicOpen_le _ hb, hb⟩
  · have hi₁ : ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ LB.wchart M (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) :=
      fun z hz => Set.mem_iInter.2 fun _ => hi hz
    have hi₂ : ⊤ ≤ x ⁻¹ᵁ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i) := fun z hz => mem_pull.2 (hi hz)
    have hW : ⊤ ≤ x ⁻¹ᵁ ((L.pull ψ).U (fun _ => k) ⊓ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i)) :=
      fun z hz => ⟨mem_pull.2 (hk hz), hi₂ hz⟩
    have l₁ : (L.pull ψ).U (fun _ => k) ⊓ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i) ≤ ψ ⁻¹ᵁ L.U k :=
      fun y hy => mem_pull.1 hy.1
    have e₁ : valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) =
        algebraMap V (FractionRing V) ϖ ^ n * valR x _ (r.f fun _ => i) := by
      refine (congrArg (valR _ _) (hϑ fun _ => i)).trans ?_
      refine (valR_res _ _ _ hi₁).trans ((valR_appLE x _ _ _ _ _ hi₂).symm.trans
        ((congrArg (valR x _) (hσ fun _ => i)).trans ((valR_mul' x _ hi₂ _ _).trans (congrArg (· * _) ?_))))
      exact (valR_res x le_top _ hi₂).trans (valR_const x _ hx _)
    have e₂ : (ψ.appLE _ _ l₁).hom (θ.f k) = (show Γ(pullback G.hom (jK V), (L.pull ψ).U (fun _ => k) ⊓
        (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i))ˣ from w.s (fun _ => k, fun _ => i)).val *
          ((pullback G.hom (jK V)).presheaf.map (homOfLE inf_le_right).op).hom (r.f fun _ => i) :=
      fn_ext fun y hy => by
        refine (gs_appLE _ _ _ _ (𝟙 _) y hy _).trans ?_
        rw [Category.id_comp, hr y k _ (l₁ hy) hy.2]
        exact ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _)
          (gs_res (𝟙 _) y _ hy _))).symm
    have e₃ := (valR_appLE x ψ _ _ l₁ _ hW).symm.trans ((congrArg (valR x _) e₂).trans
      ((valR_mul' x _ hW _ _).trans (congrArg (_ * ·) (valR_res x _ _ hW))))
    rw [e₁, e₃]
    exact mul_left_comm _ _ _

end GlobalTheory.PrimScale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialFibreProjectionAbelianPart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpecialPoints

theorem exists_torsion_lift {T M N : Type} [CommGroup T] [CommGroup M] [Group N] (i : T →* M) (q : M →* N) (n : ℕ)
    (hqi : ∀ t, q (i t) = 1) (hker : ∀ x, q x = 1 → ∃ t, i t = x) (hq : Function.Surjective q)
    (hT : ∀ t : T, ∃ s : T, s ^ n = t) (b : N) (hb : b ^ n = 1) : ∃ x, x ^ n = 1 ∧ q x = b := by
  obtain ⟨x, rfl⟩ := hq b
  obtain ⟨t, ht⟩ := hker (x ^ n) (by rw [map_pow, hb])
  obtain ⟨s, rfl⟩ := hT t
  refine ⟨x * (i s)⁻¹, ?_, ?_⟩
  · rw [mul_pow, inv_pow, ← map_pow, ht, mul_inv_cancel]
  · rw [map_mul, map_inv, hqi, inv_one, _root_.mul_one]

theorem exists_projection :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (g : GtCoord (IsLocalRing.maximalIdeal V) D 0 G) (κ : Type) [Field κ] [IsAlgClosed κ] (f : V →+* κ), IsLocalHom f → ∃ π : (Over.mk (spMap f) ⟶ G) →* (Over.mk (spMap f) ⟶ D.P.A), (∀ x, ∃ y : Sp κ ⟶ (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left, y ≫ (fstG (IsLocalRing.maximalIdeal V) 0 G).left = x.left ∧ y ≫ g.pG.left = (π x).left) ∧ ∀ n : ℕ, 1 ≤ n → ∀ b, b ^ n = 1 → ∃ x, x ^ n = 1 ∧ π x = b := by
  intro V _ _ _ D G _ _ _ c K _ _ f hf
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Sp K ⟶ Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)),
      r₀ ≫ thick V (IsLocalRing.maximalIdeal V) 0 = spMap f := by
    have h₂ : ∀ a ∈ IsLocalRing.maximalIdeal V ^ (0 + 1), f a = 0 := fun a ha => by
      rw [zero_add, pow_one] at ha
      by_contra h
      exact ha (hf.map_nonunit a (Ne.isUnit h))
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ f h₂)), ?_⟩
    rw [← Spec.map_comp]
    rfl
  have := c.q_hom
  have := c.i_hom
  have := c.q_surj
  have hk := c.isKernel
  let T : Over (Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))) := Over.mk r₀
  let eG := TorsionLift.ptsEquiv (thick V (IsLocalRing.maximalIdeal V) 0) G T _ hr₀
  let eB := TorsionLift.ptsEquiv (thick V (IsLocalRing.maximalIdeal V) 0) D.P.A T _ hr₀
  let q := IsMonHom.monoidHom c.q T
  let i := IsMonHom.monoidHom c.i T
  let e := splitTorusPointsEquiv _ D.X T
  have hqi : ∀ t, q (i t) = 1 := fun t => by
    change (t ≫ c.i) ≫ c.q = 1
    rw [Category.assoc, hk.w, ← Category.assoc, comp_toUnit]
    rfl
  have hker : ∀ x, q x = 1 → ∃ t, i t = x := fun x hx =>
    ⟨hk.lift x (toUnit _) (by rw [show x ≫ c.q = 1 from hx, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hq : Function.Surjective q := fun b => by
    have : LocallyOfFiniteType (c.q.left ≫ (thickObj V (IsLocalRing.maximalIdeal V) 0 D.P.A).hom) := by
      rw [Over.w c.q]
      exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0)))
    have : LocallyOfFiniteType c.q.left :=
      locallyOfFiniteType_of_comp _ (thickObj V (IsLocalRing.maximalIdeal V) 0 D.P.A).hom
    obtain ⟨x, hx⟩ := GeomSurj.exists_lift_of_surjective c.q.left b.left
    exact ⟨Over.homMk x (by rw [← Over.w c.q, ← Category.assoc, ← hx]; exact Over.w b),
      Over.OverMorphism.ext hx.symm⟩
  refine ⟨eB.toMonoidHom.comp (q.comp eG.symm.toMonoidHom), fun x => ?_, fun n hn b hb => ?_⟩
  · obtain ⟨x, rfl⟩ := eG.surjective x
    refine ⟨x.left, (TorsionLift.ptsEquiv_left _ _ _ _ _ x).symm, ?_⟩
    change _ = (eB (q (eG.symm (eG x)))).left
    rw [eG.symm_apply_apply]
    exact (Category.assoc _ _ _).symm.trans (TorsionLift.ptsEquiv_left _ _ _ _ _ (q x)).symm
  · obtain ⟨x, hx, hxb⟩ := exists_torsion_lift
      ((i.comp e.symm.toMonoidHom) : (Multiplicative D.X →* Γ(T.left, ⊤)ˣ) →* _) q n
      (fun t => hqi _) (fun x hx => by
        obtain ⟨t, ht⟩ := hker x hx
        exact ⟨e t, (congrArg i (e.symm_apply_apply t)).trans ht⟩) hq
      (TorsLift.exists_pow_eq_hom (M := Γ(T.left, ⊤)ˣ) n (TorsLift.exists_pow_eq_unit K n hn))
      (eB.symm b) (by rw [← map_pow, hb, map_one])
    refine ⟨eG x, by rw [← map_pow, hx, map_one], ?_⟩
    change eB (q (eG.symm (eG x))) = b
    rw [eG.symm_apply_apply, hxb, eB.apply_symm_apply]

end GlobalTheory.SpecialPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionLiftSpecialFibreOfGenericRational
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem epi_spMap_of_finite_of_injective (V W : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [Algebra V W] [Module.Finite V W]
    (hinj : Function.Injective (algebraMap V W)) : Epi (spMap (algebraMap V W)) := by
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hinj
  have hfl : Module.Flat V W := inferInstance
  have : Flat (spMap (algebraMap V W)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 hfl
  have : Surjective (spMap (algebraMap V W)) :=
    ⟨Algebra.IsIntegral.comap_surjective V W⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_torsion_lift_of_generic_rational : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (W C : Type) [CommRing W] [IsLocalRing W] [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C), IsLocalHom α → Function.Injective β → β.comp α = ga.comp (algebraMap V (FractionRing V)) → ∀ (X : Scheme.{0}) (y : Sp W ⟶ X) (x : Sp (FractionRing V) ⟶ X), spMap β ≫ y = spMap ga ≫ x → ∃ h : Sp V ⟶ X, spMap α ≫ h = y ∧ jK V ≫ h = x) → UnramExtSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] (C : Type) [Field C] [IsAlgClosed C] (ga : FractionRing V →+* C) (m : ℕ), IsUnit (m : V) → (∀ y : Over.mk (spMap ga ≫ jK V) ⟶ G, y ^ m = 1 → ∃ x : Sp (FractionRing V) ⟶ G.left, spMap ga ≫ x = y.left) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (f : V →+* κ), IsLocalHom f → ∀ x : Over.mk (spMap f) ⟶ G, x ^ m = 1 → ∃ h : baseOver (Sp V) ⟶ G, h ^ m = 1 ∧ spMap f ≫ h.left = x.left := by
  intro hD hU V _ _ _ hV G _ _ _ _ C _ _ ga m hm hrat κ _ _ f hf x hx
  obtain ⟨W, _, _, _, _, _, f', hfin, hinj, hloc, -, hcomp, hy⟩ :=
    exists_finite_extension_torsion_lift hU V G m hm κ f hf {x} (by simpa using hx)
  obtain ⟨y, hy, hy'⟩ := hy x (Finset.mem_singleton_self x)
  let : Algebra V C := (ga.comp (algebraMap V (FractionRing V))).toAlgebra
  have hC : Function.Injective (algebraMap V C) :=
    ga.injective.comp (IsFractionRing.injective V (FractionRing V))
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hinj
  have : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hC
  let β : W →ₐ[V] C := IsAlgClosed.lift
  have hβ : Function.Injective β.toRingHom := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    rw [RingHom.comap_ker]
    refine (RingHom.injective_iff_ker_eq_bot _).1 ?_
    rw [show β.toRingHom.comp (algebraMap V W) = algebraMap V C from β.comp_algebraMap]
    exact hC
  have hβα : β.toRingHom.comp (algebraMap V W) = ga.comp (algebraMap V (FractionRing V)) :=
    β.comp_algebraMap
  have hw : spMap β.toRingHom ≫ spMap (algebraMap V W) = spMap ga ≫ jK V := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hβα]
  let j : Over.mk (spMap ga ≫ jK V) ⟶ Over.mk (spMap (algebraMap V W)) :=
    Over.homMk (spMap β.toRingHom) hw
  obtain ⟨x₀, hx₀⟩ := hrat (j ≫ y) (by rw [← comp_pow, hy, comp_one])
  obtain ⟨h₀, hh₀, -⟩ := hD V W C (algebraMap V W) β.toRingHom ga hloc hβ hβα G.left y.left x₀
    hx₀.symm
  have hepi := epi_spMap_of_finite_of_injective V W hinj
  let h : baseOver (Sp V) ⟶ G := Over.homMk h₀ (by
    rw [← cancel_epi (spMap (algebraMap V W))]
    exact ((reassoc_of% hh₀) _).trans ((Over.w y).trans (Category.comp_id _).symm))
  let a : Over.mk (spMap (algebraMap V W)) ⟶ baseOver (Sp V) :=
    Over.homMk (spMap (algebraMap V W)) (Category.comp_id _)
  have ha : a ≫ h = y := Over.OverMorphism.ext hh₀
  have : Epi a.left := hepi
  have : Epi a := Over.epi_of_epi_left a
  refine ⟨h, ?_, ?_⟩
  · rw [← cancel_epi a, comp_pow, ha, hy, comp_one]
  · rw [← hy', ← hh₀, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCubicalBundleMapOfPulledBackDegenerationStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCubicalBundleMap_of_pulled_back_degeneration : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (hD : IsPullDeg φ D D'), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (pull_grp hD).1.w hD.w := by
  first | exact @GlobalTheory.DegPullPackage.isCPMap_of_isPullDeg | exact GlobalTheory.DegPullPackage.isCPMap_of_isPullDeg | (intros; apply GlobalTheory.DegPullPackage.isCPMap_of_isPullDeg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLevelStructureOfGenericOfFibrewiseIndepStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLevelStructure_of_generic_of_fibrewise_indep : Laws → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (P : PolAV (Sp R)) (P₀ : PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A (spMap (algebraMap R K)) φ → LBIso P₀.L (P.L.pull φ) → P.g = P₀.g → ∀ (M : ℕ) (ze : Rˣ) (ze₀ : Kˣ), IsUnit (M : R) → algebraMap R K ze = ze₀ → ∀ (lev₀ : Out.Level P₀ M (unitOn ze₀)) (y : Fin (2 * P.g) → (baseOver (Sp R) ⟶ P.A)), (∀ (i₀ : Fin (2 * P₀.g)) (i : Fin (2 * P.g)), (i₀ : ℕ) = i → (lev₀.pt i₀).left ≫ φ = spMap (algebraMap R K) ≫ (y i).left) → (∀ (F : Type) [Field F] [IsAlgClosed F] (s : Spec (CommRingCat.of F) ⟶ Sp R) (c c' : Fin (2 * P.g) → Fin M), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c' i : ℕ)) → c = c') → ∃ lev : Out.Level P M (unitOn ze), lev.pt = y := by
  first | exact @GlobalTheory.level_of_generic_of_indep | exact GlobalTheory.level_of_generic_of_indep | (intros; apply GlobalTheory.level_of_generic_of_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreeOrthogonalSupportAndSupISpecializesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
theorem _root_.GlobalTheory.T.isoFree_orthogonal_support_and_supI_specializes : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) := by
  first | exact @GlobalTheory.ZH.isoFree_TT_and_supI_specializes | exact GlobalTheory.ZH.isoFree_TT_and_supI_specializes | (intros; apply GlobalTheory.ZH.isoFree_TT_and_supI_specializes <;> assumption)
end

