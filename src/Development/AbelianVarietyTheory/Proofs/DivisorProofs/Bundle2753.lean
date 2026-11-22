import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointPeriodRelation
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

namespace GlobalTheory.DetHT

theorem ptAt_tangent_isEig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (z : FrPt Xo c ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X)
    (yy : Sp ℂ_[p] ⟶ Xo.XF c),
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb yy Q π ψ → ∀ (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) (xx : LieG Q.Gt),
      LieTie Q (ψ ≫ Z.m0.toSABMap.φ) xx (z.u σ j) → AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers σ) xx := by
  intro E _ _ _ H Dw l Xo c Z p _ _ z yb yy
  letI := H.starRing
  intro Q π ψ hP σ j xx h
  obtain ⟨-, -, h3, h4, h5⟩ := hP
  have hpb : IsGrpPullback Q.A.A Xo.univ.t.G _ (ψ ≫ Z.m0.toSABMap.φ) := h4.comp Z.m0.toSABMap.cart
  have hact : ∀ a, (Q.oA.act a).left ≫ (ψ ≫ Z.m0.toSABMap.φ) =
      (ψ ≫ Z.m0.toSABMap.φ) ≫ (Xo.univ.t.act.act a).left := fun a => by
    have e : (Q.oA.act a).left ≫ ψ = ψ ≫ (Z.oF.t.act.act a).left := Z.m.cart.1.hom_ext
      (by rw [Category.assoc, Category.assoc, Z.m.act, h5, ← Category.assoc ψ, h5, ← Category.assoc, Q.gen_act,
        Category.assoc, h3, Category.assoc])
      (by rw [Category.assoc, Category.assoc, Over.w, h4.1.w, Over.w_assoc])
    rw [← Category.assoc, e, Category.assoc, Category.assoc, Z.m0.toSABMap.act]
  exact fun a =>
    (h.act a (hact a)).unique hpb.1 (by rw [z.eig σ j a, ← algebraMap_embInt Q.integers]; exact h.scale _)

end GlobalTheory.DetHT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointTangentMapFormula
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

namespace GlobalTheory.DetHT.BridgeBasis

theorem mem_latHT_iff_changeBasis : BridgeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (yy : Sp ℂ_[p] ⟶ Xo.XF c) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X),
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb yy Q π ψ → ∀ (n : ℕ) (xx : Fin n → LieG Q.Gt) (u u' : Fin n → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left))
      (g : Matrix (Fin n) (Fin n) ℂ_[p]), (∀ j, IsTanAtG Z.t (yy ≫ Z.j) (u j)) →
      (∀ j, LieTie Q (Q.gen ≫ π) (xx j) (u j)) → (∀ i, IsCombAtG Z.t (yy ≫ Z.j) u (g i) (u' i)) →
      ∀ (a : Fin n → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left), IsCombAtG Z.t (yy ≫ Z.j) u' a w →
        (w ∈ GlobalTheory.ShFam.Pad.latHT Z.t p (yy ≫ Z.j) ↔ ∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT) := by
  intro hB E _ _ _ H Dw l Xo c Z p _ _ yy yb
  letI := H.starRing
  intro Q π ψ hP n xx u u' g hu hx hg a w hw
  haveI : IsProper Z.s := projProper _ _ _ Z.proj
  haveI : IsNoetherianRing (𝓞 c.F) := Algebra.FiniteType.isNoetherianRing ℤ (𝓞 c.F)
  haveI : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  haveI : Z.X.IsSeparated := ⟨by rw [← terminal.comp_from Z.s]; infer_instance⟩
  have hc : IsCombAtG Z.t (yy ≫ Z.j) u (g.transpose.mulVec a) w :=
    GlobalTheory.TangentLinear.isCombAtG_mulVec u hu u' g.transpose a w (fun i => by simpa [Matrix.transpose_apply] using hg i) hw
  rw [← hP.1] at hc
  have key := hB E H Z.X Z.t p Q yb π hP.2.1 n xx u hx (g.transpose.mulVec a) w hc
  rw [hP.1] at key
  rw [key]
  have hs : ∑ j, (g.transpose.mulVec a) j • Q.bLie (xx j) = ∑ i, a i • ∑ j, g i j • Q.bLie (xx j) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [_root_.mul_comm]
  rw [hs]

end GlobalTheory.DetHT.BridgeBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupCocycleMemCobRangeOfDiagonalSumZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem lift_counit_pullTwo {R D D' : Type} [CommRing R] [CommRing D] [Bialgebra R D] [CommRing D']
    [Bialgebra R D'] (f : D →ₐc[R] D') (c : D ⊗[R] D) :
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R D') (Bialgebra.counitAlgHom R D')
        (fun _ _ ↦ Commute.all _ _) (pullbackTwo f c) =
      Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R D) (Bialgebra.counitAlgHom R D)
        (fun _ _ ↦ Commute.all _ _) c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [pullbackTwo]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem diagSum_one (R D : Type) [CommRing R] [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) :
    diagSum R D m 1 = (m : D) := by
  rw [Algebra.TensorProduct.one_def, diagSum_tmul]
  simp

theorem cocycle_mem_range_cob_of_diagSum_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
      ∀ (G : PDivGroup p R) (z : G.cocycles), diagSum R (G.A N) (p ^ N) (z.1 N) = 0 →
        z ∈ LinearMap.range G.cob := by
  intro p _ R _ N hp G z hz
  have hq : ((p ^ N : ℕ) : R) = 0 := by rw [Nat.cast_pow, hp]
  let ε : ∀ n, G.A n ⊗[R] G.A n →ₐ[R] R := fun n =>
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R (G.A n)) (Bialgebra.counitAlgHom R (G.A n))
      (fun _ _ ↦ Commute.all _ _)
  have hr : ∀ n, ε n (z.1 n) = ε 0 (z.1 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [← ih, ← (z.2 n).2]; exact (lift_counit_pullTwo _ _).symm
  let o : G.funs := ⟨fun _ => 1, fun n => map_one (G.res n)⟩
  let z' : G.cocycles := z + ε 0 (z.1 0) • G.cob o
  have hz' : ∀ n, z'.1 n = z.1 n - ε 0 (z.1 0) • (1 : G.A n ⊗[R] G.A n) := by
    intro n
    change z.1 n + ε 0 (z.1 0) • cobOne R (G.A n) 1 = _
    rw [cobOne_apply, Bialgebra.comul_one, ← Algebra.TensorProduct.one_def, sub_self, zero_sub, smul_neg,
      sub_eq_add_neg]
  have h0 : ∀ n, ε n (z'.1 n) = 0 := by
    intro n
    rw [hz', map_sub, map_smul, map_one, hr, smul_eq_mul, _root_.mul_one, sub_self]
  have hmem : z' ∈ LinearMap.range G.cob := by
    refine cocycle_mem_range_cob_of_pullback_mulBy_pow p R G N z'
      (fun n => diagSum R (G.A n) (p ^ N) (z'.1 n)) (fun n => ?_) (fun n => ?_) ?_
    · rw [diagSum_pullTwo, (z'.2 n).2]
    · rw [cobOne_diagSum_eq p R G n (p ^ N) hq _ (z'.2 n).1]
      have := h0 n
      simp only [ε] at this
      rw [this, zero_smul, sub_zero]
    · change diagSum R (G.A N) (p ^ N) (z'.1 N) = 0
      rw [hz', map_sub, map_smul, hz, diagSum_one, ← map_natCast (algebraMap R (G.A N)), hq, map_zero,
        smul_zero, sub_zero]
  have : z = z' - ε 0 (z.1 0) • G.cob o := by simp [z']
  rw [this]
  exact Submodule.sub_mem _ hmem (Submodule.smul_mem _ _ ⟨o, rfl⟩)

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionMemBallExpOfProjArithVariety
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem sec_nsq_le {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (M : HermLB p) (u : M.B.Sec) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ C := by
  have := hX.finite_emb
  have hb : ∀ σ : k →+* ℂ, ∃ K : ℝ, ∀ y, (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ K := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨K, hK⟩ := (isCompact_range ((M.cInf σ).continuous_nsq u)).bddAbove
    exact ⟨K, fun y => hK ⟨y, rfl⟩⟩
  choose K hK using hb
  have := Fintype.ofFinite (k →+* ℂ)
  refine ⟨∑ τ, |K τ| + 1, ?_, fun σ y => (hK σ y).trans ?_⟩
  · linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)]
  · have := Finset.single_le_sum (fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)) (Finset.mem_univ σ)
    linarith [le_abs_self (K σ)]

theorem bounded_norm : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∃ u : ℝ, 0 ≤ u ∧ f ∈ P.Bl a b (Real.exp u) := by
  intro k _ X _ p D hX P a b f hf
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a b
  obtain ⟨e, -, hrng, hnu, -⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P a b M hM
  obtain ⟨u, rfl⟩ : f ∈ Set.range e := by rw [hrng]; exact hf
  obtain ⟨C, hC1, hC⟩ := sec_nsq_le hX M u
  refine ⟨Real.log C, Real.log_nonneg hC1, hf, fun σ y => ?_⟩
  rw [Real.exp_log (by linarith)]
  have h1 := hnu u σ y
  have h2 := hC σ y
  have h3 : 0 ≤ P.nu a b σ y (e u) := by unfold Pair.nu; positivity
  nlinarith

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionsFgOfProjArithVariety
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSNef.PairFG

theorem exists_hom {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (a b : ℤ)
    (M : HermLB p) (hM : P.Rep a b M) :
    ∃ φ : M.B.Sec →+ X.functionField, φ.range = P.H a b := by
  obtain ⟨ρ, hρ, hu, -⟩ := hM
  obtain ⟨e, he⟩ := RepDict.exists_quot M.isLB hρ
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  obtain ⟨c₀, h₀⟩ := hcov M.isLB (genericPoint X)
  have hρ₀ := (ρ c₀).ne_zero
  let φ : M.B.Sec →+ X.functionField :=
    { toFun := e
      map_zero' := by
        refine mul_right_cancel₀ hρ₀ ?_
        rw [he 0 c₀ h₀, zero_mul]
        exact map_zero _
      map_add' := fun u v => by
        refine mul_right_cancel₀ hρ₀ ?_
        rw [he (u + v) c₀ h₀, add_mul, he u c₀ h₀, he v c₀ h₀]
        exact map_add _ _ _ }
  have hl (f : X.functionField) c i j :
      P.loc a b f i j * ((ρ c : X.functionField) / P.loc a b 1 i j) = f * ρ c := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    simp only [Pair.loc]
    field_simp
  have hl' (f : X.functionField) c i j :
      P.loc a b f i j = f * ρ c * ((ρ c : X.functionField) / P.loc a b 1 i j)⁻¹ := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    have := (ρ c).ne_zero
    simp only [Pair.loc]
    field_simp
  refine ⟨φ, le_antisymm ?_ fun f hf => ?_⟩
  · rintro _ ⟨u, rfl⟩ x i j hi hj
    obtain ⟨c, hc⟩ := hcov M.isLB x
    change RegAt x (P.loc a b (e u) i j)
    rw [hl' _ c, he u c (gen_mem hc)]
    exact (regAt_fnOf hc _ _).mul (hu x c i j hc hi hj).inv.regAt
  · obtain ⟨u, hu'⟩ := RepDict.exists_sec hρ (f := f) fun c x hc => by
      obtain ⟨i, hi⟩ := hcov P.L.isLB x
      obtain ⟨j, hj⟩ := hcov P.A.isLB x
      rw [← hl f c i j]
      exact (hf x i j hi hj).mul (hu x c i j hc hi hj).regAt
    exact ⟨u, mul_right_cancel₀ hρ₀ ((he u c₀ h₀).trans (hu' c₀ h₀))⟩

theorem h_fg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a b : ℤ), (P.H a b).FG := by
  intro k _ X _ p D hX P a b
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a b
  obtain ⟨φ, hφ⟩ := exists_hom P a b M hM
  have := GlobalTheory.T.addGroupFG_lineBundleSections_arithmeticVariety k X p D hX M.B M.isLB
  rw [← hφ, AddMonoidHom.range_eq_map]
  classical
  obtain ⟨S, hS⟩ := this.out
  exact ⟨S.image φ, by rw [Finset.coe_image, ← AddMonoidHom.map_closure, hS]⟩

end GlobalTheory.HSNef.PairFG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairUOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

abbrev sqR (N : Near π G) : Over (Sp R) :=
  Over.mk ((Desc.UT N ⊗ Desc.UT N).hom ≫ pullback.fst π π ≫ π)

def fstU (N : Near π G) : sqR N ⟶ N.U :=
  Over.homMk ((fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (fst (Desc.UT N) (Desc.UT N)))))))

def sndU (N : Near π G) : sqR N ⟶ N.U :=
  Over.homMk ((snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (snd (Desc.UT N) (Desc.UT N)))))))

def pairU (N : Near π G) : (Desc.UT N ⊗ Desc.UT N).left ⟶ (N.U ⊗ N.U).left :=
  (lift (fstU N) (sndU N)).left

abbrev VT (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) : (Desc.UT N ⊗ Desc.UT N).left.Opens :=
  pairU N ⁻¹ᵁ V

theorem pairU_over (N : Near π G) :
    pairU N ≫ (N.U ⊗ N.U).hom = (Desc.UT N ⊗ Desc.UT N).hom ≫ pullback.fst π π ≫ π :=
  Over.w (lift (fstU N) (sndU N))

def mT (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) : (VT N V).toScheme ⟶ (Desc.UT N).left :=
  pullback.lift ((pairU N ∣_ V) ≫ m) ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) (by
    have e : (pairU N ∣_ V) ≫ V.ι = (VT N V).ι ≫ pairU N := morphismRestrict_ι _ _
    refine (Category.assoc _ _ _).trans ?_
    rw [hm, ← Category.assoc, e, Category.assoc, pairU_over, Category.assoc])

variable [GrpObj G]

def trip (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N ⟶ (Over.pullback p).obj G :=
  (snd _ _ ≫ Desc.emb N p hp)⁻¹ * (fst _ _ ≫ Desc.sum N p hp)

def Pk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Over (pullback π π) :=
  Over.mk (pullback.snd (Desc.emb N p hp).left (trip N p hp).left ≫ ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom)

def dP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Pk N p hp ⟶ Desc.UT N :=
  Over.homMk (pullback.fst _ _) (by
    show pullback.fst _ _ ≫ (Desc.UT N).hom = pullback.snd _ _ ≫ _
    rw [← Over.w (Desc.emb N p hp), ← Category.assoc, pullback.condition, Category.assoc, Over.w (trip N p hp)])

def abP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ Desc.UT N ⊗ Desc.UT N :=
  Over.homMk (pullback.snd _ _ ≫ (fst (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)).left)
    ((Category.assoc _ _ _).trans (congrArg (pullback.snd _ _ ≫ ·) (Over.w (fst (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)))))

def cP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Pk N p hp ⟶ Desc.UT N :=
  Over.homMk (pullback.snd _ _ ≫ (snd (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)).left)
    ((Category.assoc _ _ _).trans (congrArg (pullback.snd _ _ ≫ ·) (Over.w (snd (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)))))

def cdP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ Desc.UT N ⊗ Desc.UT N :=
  lift (cP N p hp) (dP N p hp)

def Wk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (V : (N.U ⊗ N.U).left.Opens) :
    (Pk N p hp).left.Opens :=
  (abP N p hp).left ⁻¹ᵁ VT N V ⊓ (cdP N p hp).left ⁻¹ᵁ VT N V

def q3 (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N :=
  Over.homMk (pullback.snd _ _) rfl

theorem abP_eq (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    abP N p hp = q3 N p hp ≫ fst _ _ := Over.OverMorphism.ext rfl

theorem indicatorIdempotent_eq_add_sum (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    cP N p hp = q3 N p hp ≫ snd _ _ := Over.OverMorphism.ext rfl

theorem dP_emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    dP N p hp ≫ Desc.emb N p hp = q3 N p hp ≫ trip N p hp := Over.OverMorphism.ext pullback.condition

theorem abP_sum (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    abP N p hp ≫ Desc.sum N p hp = cdP N p hp ≫ Desc.sum N p hp := by
  have e4 : cdP N p hp ≫ Desc.sum N p hp = (cP N p hp ≫ Desc.emb N p hp) * (dP N p hp ≫ Desc.emb N p hp) := by
    rw [cdP, Desc.sum, comp_mul, ← Category.assoc, lift_fst, ← Category.assoc, lift_snd]
  rw [e4, dP_emb, trip, comp_mul, GrpObj.comp_inv, indicatorIdempotent_eq_add_sum, abP_eq]
  simp only [Category.assoc]
  exact (mul_inv_cancel_left _ _).symm

theorem exists_lift (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (Z : Scheme.{0})
    (g g' : Z ⟶ (Desc.UT N ⊗ Desc.UT N).left) (h : g ≫ (Desc.sum N p hp).left = g' ≫ (Desc.sum N p hp).left) :
    ∃ z : Z ⟶ (Pk N p hp).left, z ≫ (abP N p hp).left = g ∧ z ≫ (cdP N p hp).left = g' := by
  let FinalForm : Over (pullback π π) := Over.mk (g ≫ (Desc.UT N ⊗ Desc.UT N).hom)
  have hw : g' ≫ (Desc.UT N ⊗ Desc.UT N).hom = g ≫ (Desc.UT N ⊗ Desc.UT N).hom := by
    rw [← Over.w (Desc.sum N p hp), ← Category.assoc, ← h, Category.assoc]
  let a : FinalForm ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk g rfl
  let b : FinalForm ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk g' hw
  have hab : a ≫ Desc.sum N p hp = b ≫ Desc.sum N p hp := Over.OverMorphism.ext h
  let t : FinalForm ⟶ (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N := lift a (b ≫ fst _ _)
  have ht : (b ≫ snd _ _) ≫ Desc.emb N p hp = t ≫ trip N p hp := by
    rw [trip, comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_snd, ← Category.assoc t, lift_fst, hab, Desc.sum,
      comp_mul]
    simp only [Category.assoc]
    exact (inv_mul_cancel_left _ _).symm
  let zo : FinalForm ⟶ Pk N p hp := Over.homMk (pullback.lift (b ≫ snd _ _).left t.left (congrArg Over.Hom.left ht))
    (by show pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ _ = _
        rw [← Category.assoc, pullback.lift_snd]; exact Over.w t)
  have h1 : zo ≫ abP N p hp = a := by rw [abP_eq, ← Category.assoc]; exact (congrArg (· ≫ fst _ _)
    (Over.OverMorphism.ext (pullback.lift_snd _ _ _) : zo ≫ q3 N p hp = t)).trans (lift_fst _ _)
  have h2 : zo ≫ cdP N p hp = b := by
    have hc : zo ≫ cP N p hp = b ≫ fst _ _ := by
      rw [indicatorIdempotent_eq_add_sum, ← Category.assoc]; exact (congrArg (· ≫ snd _ _)
        (Over.OverMorphism.ext (pullback.lift_snd _ _ _) : zo ≫ q3 N p hp = t)).trans (lift_snd _ _)
    have hd : zo ≫ dP N p hp = b ≫ snd _ _ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    rw [cdP, comp_lift, hc, hd]
    exact (lift_comp_fst_snd b)
  exact ⟨zo.left, congrArg Over.Hom.left h1, congrArg Over.Hom.left h2⟩

end GlobalTheory.Mum.DescKP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

def isoVal {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B₁]
    [IsCommMonObj B₁] [GrpObj B'] {M : LB B.left} {M₁ : LB B₁.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    {β₂' : (G2 B').left ⟶ (G2 B₁).left} (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂'))
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B₁.left) → M₁.ι) (J' : (Z ⟶ B.left) → M.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm p z _ (w.s (fun _ I => J (p ≫ β₂' ≫ (psum B₁ (x2 B₁) I.down).left),
    fun _ I => J' (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)))

def IsNormIso {R : Type} [CommRing R] [IsDomain R] {S S₁ : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over (Sp R)}
    [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B'] {M : LB B.left} {M₁ : LB B₁.left}
    {β₂ : (G2 B').left ⟶ (G2 B).left} {β₂' : (G2 B').left ⟶ (G2 B₁).left}
    (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')) : Prop :=
  ∀ z J J', Good M₁ z J → Good M z J' → isoVal w (lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left z J J' = 1

def PeriodRel {o V V₁ W : Type} [CommRing o] [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [CommRing W]
    [IsLocalRing W] (D : DegPre V) (T : TautBase o W) (f₁ : V →+* V₁) (κ₁ : W →+* V₁) {B' : Over (Sp V₁)} [GrpObj B']
    {β₂ : (G2 B').left ⟶ (G2 D.P.A).left} {β₂' : (G2 B').left ⟶ (G2 T.B).left}
    (w : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (c : (Fin T.r → ℤ) ≃+ D.X)
    (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (n : ℕ) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ) :
    Prop :=
  ∀ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ → ∀ a b z J J', Good T.M.L z J → Good D.P.L z J' →
    val (D.tau (c a) (c b)) κK z J' = gm (𝟙 (TK V₁).left) z ⊤ (unitOn (q a b)) *
      (isoVal w (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x b)).left z J J' *
        val (T.τ₀ ((n : ℤ) • a) ((n : ℤ) • b)) ((TK V₁).hom ≫ spMap κ₁) z J)

end GlobalTheory.TChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicHolomorphicSectionsRegularAbelianVarietyStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_holomorphic_sections_regular_abelianVariety : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ σ : M.ι → (Fin g → ℂ) → ℂ, (∀ i, DifferentiableOn ℂ (σ i) (pre u.ex (M.U i))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (M.U i), σ i (z + l) = σ i z) → (∀ i j, ∀ z ∈ pre u.ex (M.U i ⊓ M.U j), σ i z = val u.ex _ (M.g i j).val z * σ j z) → ∀ i, IsReg u.ex (M.U i) (σ i) := by
  first | exact @GlobalTheory.PeriodicSecAlg.main | exact GlobalTheory.PeriodicSecAlg.main | (intros; apply GlobalTheory.PeriodicSecAlg.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsBoundedOutsideCmTypeOfDefiniteArcLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_bounded_outside_cmType_of_definite_arc_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → (U.X k).p0 = 0 → ∀ v : Fin N → E, ∃ C : ℝ, ∀ᶠ w in imTop, ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C := by
  first | exact @GlobalTheory.ShFam.PerLim.periods_bounded_outside_cmType_of_definite_arc_lift_alt | exact GlobalTheory.ShFam.PerLim.periods_bounded_outside_cmType_of_definite_arc_lift_alt | (intros; apply GlobalTheory.ShFam.PerLim.periods_bounded_outside_cmType_of_definite_arc_lift_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormHeckeProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_norm_hecke_product : GlobalTheory.FunPr.Hypotheses₂ → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ t : T, ∃ (P : PolF D WW.rank A.rank) (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)) (c : ℂ), c ≠ 0 ∧ ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ WW) 𝓕 ν ∧ ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ → ((∫ h in 𝓕, ‖X.I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) = c * ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s := by
  first | exact @GlobalTheory.RallisBottom.normBig_innerProduct | exact GlobalTheory.RallisBottom.normBig_innerProduct | (intros; apply GlobalTheory.RallisBottom.normBig_innerProduct <;> assumption)
end

