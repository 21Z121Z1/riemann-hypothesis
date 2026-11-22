import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ConclusionNotEmpty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0149
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.LinEndOfOLinear
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.EndModel
open ReciprocityTheory.ChartRestriction.G.Out.InhTate

theorem endData_tate (m : ℤ) :
    EndData tatePre (𝟙 _) (𝟙 _) (AddMonoidHom.mulLeft m) (AddMonoidHom.mulLeft m) := by
  refine ⟨inferInstance, inferInstance, GlobalTheory.BoxPowerProbe.rosati_tate, fun _ => (Category.comp_id _).symm,
    fun _ => (Category.comp_id _).symm, ?_⟩
  exact (GlobalTheory.BoxPowerProbe.tauBal_tate_iff _ _).2 fun y y' => by
    show m * y * y' = y * (m * y'); ring

theorem not_endData_tate :
    ¬ EndData tatePre (𝟙 _) (𝟙 _) 0 (AddMonoidHom.id _) := fun h => by
  have := (GlobalTheory.BoxPowerProbe.tauBal_tate_iff _ _).1 h.2.2.2.2.2 1 1
  change (0 : ℤ) * 1 = 1 * 1 at this
  simp at this

theorem endData_of_oAct {R : Type} [CommRing R] [IsDomain R] (O : Type) [Ring O] [StarRing O] (D : DegPre R)
    [Module O D.X] (io : D.OAct O) (a : O) :
    EndData D (io.onB.act a) (io.onB.act (star a)) (DistribSMul.toAddMonoidHom D.X a)
      (DistribSMul.toAddMonoidHom D.X (star a)) :=
  ⟨io.onB.hom a, io.onB.hom (star a), io.onB.rosati a, io.c_lin a, io.c_lin (star a), io.tau_bal a⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem torusEndOf_id {S : Scheme.{0}} (X : Type) [AddCommGroup X] :
    TorusEndOf X (AddMonoidHom.id X) (𝟙 (splitTorus S X)) :=
  (GlobalTheory.LinearUnifCheck.torusEndOf_iff _ _).2 fun χ => by simp

theorem linEnd_id (U : UnifPre I D A G) : LinEnd U (𝟙 _) (AddMonoidHom.id _) (𝟙 G) := by
  refine ⟨inferInstance, fun e => by simpa using (inferInstance : IsMonHom (𝟙 _)), fun e => by simp,
    fun e => by simp, fun e => ⟨𝟙 _, torusEndOf_id _, by simp⟩⟩

theorem thickMap_map {G H : Over (Sp R)} (b : G ⟶ H) (e : ℕ) :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map b).left =
      ((Over.pullback (thick R I e)).map b).left ≫ thickMap R I e H := by
  apply pullback.hom_ext
  · simp only [thickMap, pullback.map, Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
    rfl
  · simp only [thickMap, pullback.map, Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    simp
    erw [pullback.lift_snd_assoc]

theorem linEnd_of_oLinear (U : UnifPre I D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X]
    (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O) (hl : U.OLinear O ιD ιA ιG) (a : O) :
    LinEnd U (ιD.onB.act a) (DistribSMul.toAddMonoidHom D.toPre.X (star a)) (ιG.act a) := by
  have := ιG.hom a
  refine ⟨this, fun e => inferInstance, fun e => thickMap_map _ e, fun e => hl.q_lin e a, fun e => ?_⟩
  obtain ⟨t, ht, hi⟩ := hl.i_lin e a
  exact ⟨t, ht, hi⟩

theorem extLam_lam (L : LB G.left) (hL : L.IsLB) :
    ExtLam G (L.pull (pullback.fst G.hom (jK R))) (abelian₂ G L) := by
  refine ⟨LB.isLB_linComb hL _ _, fun κ₂ hκ => ?_⟩
  exact GlobalTheory.LamPull.lbIso_lam_pull (isGrpPullback_pullback G (jK R)) hL (pull_isLB hL _)
    ⟨idIso _, idIso_isGen (pull_isLB hL _)⟩ hκ

theorem exists_model : ∃ (A : PolAV (Sp (FractionRing (PowerSeries ℚ)))) (G : Over (Sp (PowerSeries ℚ))) (_ : GrpObj G)
    (_ : IsCommMonObj G) (D : DegData (PowerSeries ℚ) (maximalIdeal (PowerSeries ℚ)))
    (U : Unif (maximalIdeal (PowerSeries ℚ)) D A G), LinEnd U.toUnifPre (𝟙 _) (AddMonoidHom.id _) (𝟙 G) ∧
      Module.finrank ℤ D.toPre.X = 1 ∧
      ExtLam G (U.LG.L.pull (pullback.fst G.hom (jK _))) (abelian₂ G U.LG.L) := by
  obtain ⟨A, G, _, _, D, U, -, -, hX, -⟩ := GlobalTheory.TateUnif.exists_unif_rank_one
  exact ⟨A, G, _, _, D, U, linEnd_id _, hX, extLam_lam _ U.LG.isLB⟩

end GlobalTheory.Mum.EndModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegJoin

open GlobalTheory.SiegMin GlobalTheory.Poinc GlobalTheory.PolDeg

variable {g n : ℕ}

def MinAt5 (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) : Prop :=
  ∃ (o' : Type) (_ : CommRing o') (β : cycAway n →+* o') (S' : Scheme.{0}) (s' : S' ⟶ Sp o') (U : S'.Opens)
    (c : U.toScheme ⟶ F.X) (π : S' ⟶ Z) (G : Over S') (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left)
    (_ : IsCommMonObj G) (N : ℕ),
    (IsThetaCompact F z i ∧ IsProjOver z ∧ IsNormalScheme Z ∧ i ≫ z = F.s ∧ Dense (Set.range i) ∧ OZ.IsLB ∧ IsAmpleLB OZ) ∧
    (β.Finite ∧ Function.Injective β ∧ IsProjOver s' ∧ IsNormalScheme S' ∧ Dense (U : Set S') ∧ IsFinite c ∧
      Surjective c ∧ U.ι ≫ π = c ≫ i ∧ π ≫ z = s' ≫ spMap β ∧ Surjective π ∧ IsProper π ∧
      IsNoetherian Z) ∧
    (IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧
      IsGrpPullback ((Over.pullback c).obj F.univ.A) G U.ι e) ∧
    (1 ≤ N ∧ LBIso (OZ.pull π) (lbPow (hodge G g) N))

theorem MinAt5.isThetaCompact {F : SFam g n (zetaAway n)} {Z : Scheme.{0}} {z : Z ⟶ Sp (cycAway n)} {i : F.X ⟶ Z} {OZ : LB Z}
    (h : MinAt5 F z i OZ) : IsThetaCompact F z i ∧ OZ.IsLB ∧ IsAmpleLB OZ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨h₁, -, -, -, -, h₂, h₃⟩, -⟩ := h
  exact ⟨h₁, h₂, h₃⟩

def MinSt5 : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n),
    ∃ (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z), MinAt5 F z i OZ

def ChartSt5 : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n →
    ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ)
      (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S),
      MinAt5 F z i OZ → BlowAt F z i φ d π j BD →
      SmoothOfRelativeDimension (g * (g + 1) / 2) (π ≫ z) ∧ ∀ x : S, PreChart F (π ≫ z) j φ BD d x

def DescSt5 : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, ∀ n : ℕ, 3 ≤ n → Odd n →
    ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (d : ℕ)
      (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S),
      BlowAt F z i φ d π j BD → (∀ x : S, PreChart F (π ≫ z) j φ BD d x) →
      ∃ (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left), IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧
        IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j

end GlobalTheory.SiegJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l}

section Ord

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω)

def UOrdGe (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) ∧
    ∃ w : T.V, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def UOrdEq (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  ∃ w : T.Vˣ, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def UThroughU {X X' : Scheme.{0}} (U₀ : M.Z.Opens) (u₀ : U₀.toScheme ⟶ X) (a : X' ⟶ X) (cc : X' ⟶ Xo.XF c)
    (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) : Prop :=
  ∃ (ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme) (ξ₁ : Sp (FractionRing T.V) ⟶ X'),
    ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ ξ₀ ≫ u₀ = ξ₁ ≫ a ∧ ξ₁ ≫ cc = T.y

section API

variable {M} {T : UTrait Xo c} {ξ : Sp T.V ⟶ M.Z} {x y : Ω} {a b : ℕ}

theorem specializes_genericImage (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) (v : Sp (FractionRing T.V)) :
    (jK T.V ≫ ξ) v ⤳ (jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V)) := by
  rw [Subsingleton.elim v (IsLocalRing.closedPoint (FractionRing T.V))]

theorem UOrdGe.mem_O (h : UOrdGe M T ξ x a) :
    x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) :=
  h.1

theorem UOrdEq.val_ne_zero (h : UOrdEq M T ξ x a) : M.val (jK T.V ≫ ξ) x ≠ 0 := by
  obtain ⟨u, hu⟩ := h
  rw [hu, map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))]
  exact mul_ne_zero (pow_ne_zero _ T.irr.ne_zero) u.ne_zero

theorem UOrdEq.mem_O (h : UOrdEq M T ξ x a) :
    x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) := by
  by_contra hx
  exact h.val_ne_zero (RatModel.val_of_notMem _ hx)

theorem UOrdEq.ordGe (h : UOrdEq M T ξ x a) : UOrdGe M T ξ x a :=
  ⟨h.mem_O, h.elim fun w hw => ⟨w, hw⟩⟩

theorem UOrdGe.mono (h : UOrdGe M T ξ x a) (hba : b ≤ a) : UOrdGe M T ξ x b := by
  obtain ⟨hx, w, hw⟩ := h
  refine ⟨hx, T.ϖ ^ (a - b) * w, ?_⟩
  rw [hw, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hba]

theorem UOrdGe.le_of_ordEq (h : UOrdGe M T ξ x b) (h' : UOrdEq M T ξ x a) : b ≤ a := by
  obtain ⟨-, w, hw⟩ := h
  obtain ⟨u, hu⟩ := h'
  have e := IsFractionRing.injective T.V (FractionRing T.V) (hw.symm.trans hu)
  have hd : T.ϖ ^ b ∣ T.ϖ ^ a := (Units.dvd_mul_right (u := u)).1 ⟨w, e.symm⟩
  exact (pow_dvd_pow_iff T.irr.ne_zero T.irr.not_isUnit).1 hd

theorem UOrdEq.unique (h : UOrdEq M T ξ x a) (h' : UOrdEq M T ξ x b) : a = b :=
  le_antisymm (h.ordGe.le_of_ordEq h') (h'.ordGe.le_of_ordEq h)

theorem uOrdEq_one (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) : UOrdEq M T ξ 1 0 :=
  ⟨1, by rw [RatModel.val_one, pow_zero, Units.val_one, mul_one, map_one]⟩

theorem UOrdGe.add (hx : UOrdGe M T ξ x a) (hy : UOrdGe M T ξ y a) : UOrdGe M T ξ (x + y) a := by
  obtain ⟨hx0, w, hw⟩ := hx
  obtain ⟨hy0, w', hw'⟩ := hy
  refine ⟨Subalgebra.add_mem _ hx0 hy0, w + w', ?_⟩
  rw [RatModel.val_add (specializes_genericImage T ξ) hx0 hy0, hw, hw', ← map_add, mul_add]

theorem UOrdGe.mul (hx : UOrdGe M T ξ x a) (hy : UOrdGe M T ξ y b) : UOrdGe M T ξ (x * y) (a + b) := by
  obtain ⟨hx0, w, hw⟩ := hx
  obtain ⟨hy0, w', hw'⟩ := hy
  refine ⟨Subalgebra.mul_mem _ hx0 hy0, w * w', ?_⟩
  rw [RatModel.val_mul (specializes_genericImage T ξ) hx0 hy0, hw, hw', ← map_mul, pow_add]
  congr 1
  ring

theorem UOrdEq.mul (hx : UOrdEq M T ξ x a) (hy : UOrdEq M T ξ y b) : UOrdEq M T ξ (x * y) (a + b) := by
  have e := RatModel.val_mul (specializes_genericImage T ξ) hx.mem_O hy.mem_O
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  refine ⟨u * v, ?_⟩
  rw [e, hu, hv, ← map_mul, pow_add, Units.val_mul]
  congr 1
  ring

theorem UOrdGe.ordEq_zero_of_inv (h0 : x ≠ 0) (hx : UOrdGe M T ξ x 0) (hi : UOrdGe M T ξ x⁻¹ 0) : UOrdEq M T ξ x 0 := by
  have e := RatModel.val_mul (specializes_genericImage T ξ) hx.1 hi.1
  obtain ⟨-, w, hw⟩ := hx
  obtain ⟨-, w', hw'⟩ := hi
  rw [mul_inv_cancel₀ h0, RatModel.val_one, hw, hw', ← map_mul, ← map_one (algebraMap T.V (FractionRing T.V))] at e
  have e' := IsFractionRing.injective T.V (FractionRing T.V) e
  simp only [pow_zero, one_mul] at e'
  exact ⟨(IsUnit.of_mul_eq_one w' e'.symm).unit, hw⟩

example (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) : ¬ UOrdGe M T ξ 1 1 :=
  fun h => absurd (h.le_of_ordEq (uOrdEq_one T ξ)) (by omega)

example (h0 : x ≠ 0) (hx : UOrdGe M T ξ x 1) : ¬ UOrdGe M T ξ x⁻¹ 0 := fun hi =>
  absurd (hx.le_of_ordEq ((hx.mono (Nat.zero_le 1)).ordEq_zero_of_inv h0 hi)) (by omega)

end API

def ULocTuples {X X' : Scheme.{0}} (U₀ : M.Z.Opens) (u₀ : U₀.toScheme ⟶ X) (a : X' ⟶ X) (cc : X' ⟶ Xo.XF c)
    (φ : InvFun (𝓞 E)) (ι : ℕ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (Jk : K → Type) (_ : ∀ k, Fintype (Jk k)) (t : ∀ k, Jk k → Ω),
    (∀ k j, t k j ≠ 0) ∧ ∀ x : M.Z, ∃ k, ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), UThroughU M U₀ u₀ a cc T ξ →
      ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧
        (∀ j, UOrdGe M T ξ (t k j) a) ∧ ∃ j, UOrdEq M T ξ (t k j) a

variable {M}

theorem ULocTuples.exists_nat {X X' : Scheme.{0}} {U₀ : M.Z.Opens} {u₀ : U₀.toScheme ⟶ X} {a : X' ⟶ X}
    {cc : X' ⟶ Xo.XF c} {φ : InvFun (𝓞 E)} {ι : ℕ} (h : ULocTuples M U₀ u₀ a cc φ ι) {T : UTrait Xo c} {ξ : Sp T.V ⟶ M.Z}
    (hT : UThroughU M U₀ u₀ a cc T ξ) : ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be := by
  obtain ⟨_, _, _, _, t, -, h⟩ := h
  obtain ⟨k, hk⟩ := h (ξ (IsLocalRing.closedPoint T.V))
  obtain ⟨n, hn, -⟩ := hk T ξ hT specializes_rfl
  exact ⟨n, hn⟩

end Ord

def UTraitExtSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V →
    ∀ y : Sp (FractionRing V) ⟶ Xo.XF c,
      ∃ (T : UTrait Xo c) (f : V →+* T.V) (fK : FractionRing V →+* FractionRing T.V), Function.Injective f ∧
        IsLocalHom f ∧ f.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap T.V _ (f a)) ∧ T.y = spMap fK ≫ y

def UTraitUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (T T' : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (f : T.V →+* W)
    (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W) (fK' : FractionRing T'.V →+* FractionRing W),
    GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → Function.Injective f → Function.Injective f' → IsLocalHom f →
    IsLocalHom f' → (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) →
    (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) → spMap fK ≫ T.y = spMap fK' ≫ T'.y →
    ∀ (w : W) (m m' : ℕ), Irreducible w → Associated (f T.ϖ) (w ^ m) → Associated (f' T'.ϖ) (w ^ m') →
      ∃ e : T.P.D.toPre.X ≃ₗ[𝓞 E] T'.P.D.toPre.X, ∀ a b, (m : ℤ) * T.be a b = m' * T'.be (e a) (e b)

def UPoinOnX (Xo : Moduli D l) (c : Coeff l) (φ : InvFun (𝓞 E)) {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z)
    (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) (BD : EffCartierData S) :
    Prop :=
  (IsProjOver zs ∧ IsNormalScheme Z ∧ IsOpenImmersion i ∧ Dense (Set.range i) ∧ i ≫ zs = pullback.snd _ _ ∧
    OZ.IsLB ∧ IsAmpleLB OZ) ∧
  (1 ≤ N ∧ ∀ (Y : Model Xo c (RingHom.id c.F)) (f : Y.X ⟶ Z), Y.j ≫ f = i → (GlobalTheory.FlagMod.detOm Y).IsLB →
    LBIso (OZ.pull f) (lbPow (GlobalTheory.FlagMod.detOm Y) N)) ∧
  (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)),
    Nonempty (PELUnif (maximalIdeal R) t) → ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, GenOf Xo c y t →
      ∀ σ : Sp R ⟶ Sp c.F, jK R ≫ σ = y ≫ pullback.snd _ _ → ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ≫ i ∧ ξ ≫ zs = σ) ∧
  (1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ UValOn Xo c i φ J d) ∧
  (GlobalTheory.Poinc.IsNormBl π J ∧ IsProjOver (π ≫ zs) ∧ IsOpenImmersion j ∧ Dense (Set.range j) ∧ j ≫ π = i ∧
    π ⁻¹' Set.range i = Set.range j ∧ BD.idealSheaf = J.comap π ∧ UValOn Xo c j φ BD.idealSheaf d) ∧
  ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (OZ.pull π) k) (CechPic.dual BD.lb))

def UPoinStX : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
      ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l),
        ∃ (Z : Scheme.{0}) (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData)
          (S : Scheme.{0}) (π : S ⟶ Z) (j : Xo.XF c ⟶ S) (BD : EffCartierData S), UPoinOnX Xo c φ zs i OZ N d J π j BD

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.TorusPart

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Eq8

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
  {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']

def genMap (U : Unif (maximalIdeal R) D A G) : A.A.left ⟶ G.left :=
  U.gen.inv.left ≫ pullback.fst G.hom (jK R)

def TorMatch (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left)
    (ρ : D.toPre.X →+ D'.toPre.X) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F],
    (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r))) →
    ∀ (k : ℕ), IsUnit (k : R) → ∀ (τ : Multiplicative D.toPre.X →* Fˣ) (τ' : Multiplicative D'.toPre.X →* Fˣ)
      (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := V) F ⟶ A'.A),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g →
      q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g → QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' →
      a.left ≫ genMap U = a'.left ≫ genMap U' ≫ β

def Spread (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left)
    (ρ : D.toPre.X →+ D'.toPre.X) : Prop :=
  ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsDiscreteValuationRing V₁) (ψ : R →+* V₁)
    (G₁ : Over (Sp V₁)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (φ₁ : G₁.left ⟶ G.left)
    (Ω : Type) (_ : Field Ω) (α : V₁ →+* Ω) (b : V →+* Ω) (hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0)
    (GΩ : Over (Sp Ω)) (_ : GrpObj GΩ) (n : GΩ.left ⟶ G₁.left) (hn : IsGrpPullback GΩ G₁ (spMap α) n)
    (n' : GΩ.left ⟶ G'.left) (hn' : IsGrpPullback GΩ G' (spMap b) n') (j : splitTorus (Sp V₁) D'.toPre.X ⟶ G₁)
    (G₀ : Over (Sp (ResidueField V₁))) (_ : GrpObj G₀) (m₀ : G₀.left ⟶ G₁.left)
    (hm₀ : IsGrpPullback G₀ G₁ (spMap (residue V₁)) m₀)
    (h₀ : ∀ x ∈ maximalIdeal R ^ (0 + 1), (residue V₁).comp ψ x = 0)
    (hm₀' : IsGrpPullback G₀ G (spMap ((residue V₁).comp ψ)) (m₀ ≫ φ₁)),
    IsLocalHom ψ ∧ IsGrpPullback G₁ G (spMap ψ) φ₁ ∧ IsMonHom j ∧ Function.Injective α ∧ α.comp ψ = b.comp g ∧
      n ≫ φ₁ = n' ≫ β ∧ pullTorus hn j = gtTorus (U'.gt 0) hb hn' ∧
      pullTorus hm₀ j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ gtTorus (U.gt 0) h₀ hm₀'

end GlobalTheory.Poinc.Eq8
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.UApproxAtZero
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
namespace GlobalTheory.UPoinc.UModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def valInt (t : UCTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* OO p :=
  (RatModel.valLoc t.y z₁ (specializes_of_eq t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem val_eq_valInt (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : t.val a = (valInt t a : PadicAlgCl p) :=
  RatModel.val_spMap_comp (OO p).subtype t.y (specializes_of_eq t.cen) (X₁.M.stalkEquiv z₁ a)

theorem norm_val_le (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖t.val a‖ ≤ 1 := by
  rw [val_eq_valInt]
  have h : Valued.v (valInt t a : PadicAlgCl p) ≤ 1 := (valInt t a).2
  exact_mod_cast h

theorem sc_pos (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  set x := algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ with hx
  have h0 : x ≠ 0 := fun h => t.T.irr.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h)
  have h1 : 0 < ‖t.ι x‖ := norm_pos_iff.2 ((map_ne_zero t.ι).2 h0)
  have h2 : ‖t.ι x‖ < 1 := by
    by_contra h
    have : ‖t.ι x⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.1 h)
    obtain ⟨v, hv⟩ := (t.int _).1 this
    refine t.T.irr.not_isUnit (IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing t.T.V) ?_))
    rw [map_mul, map_one, hv, ← hx, mul_inv_cancel₀ h0]
  exact neg_pos.2 (Real.log_neg h1 h2)

theorem uApproxAt_zero (φ : GlobalTheory.LocM.InvFun (𝓞 E)) : UApproxAt X₁ φ 0 := fun p _ z₁ t₀ e =>
  ⟨1, by simp [val_eq_valInt], fun t => Or.inl (by simp [val_eq_valInt])⟩

end GlobalTheory.UPoinc.UModel
end
end

