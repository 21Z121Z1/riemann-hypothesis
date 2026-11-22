import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSmConnOfIsProper
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmConnProper

theorem isAbelianScheme_of_smConn_of_isProper (S : Scheme.{0}) (G : Over S) [GrpObj G]
    (h : GlobalTheory.SS.SmConn G) (hp : IsProper G.hom) : IsAbelianScheme G :=
  ⟨h.1, h.2.1, hp, h.2.2.2.2⟩

theorem main : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], GlobalTheory.SS.SmConn G → IsProper G.hom → IsAbelianScheme G :=
  fun S G _ h hp => isAbelianScheme_of_smConn_of_isProper S G h hp

end GlobalTheory.SmConnProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfThickeningsLocal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AlgGroup

open GlobalTheory.LN GlobalTheory.UU GlobalTheory.AbLaw.Seesaw

theorem isPullback_of_isGrpPullback {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B']
    {f : S' ⟶ S} {F : B'.left ⟶ B.left} (h : IsGrpPullback B' B f F) : IsPullback F B'.hom B.hom f := h.1

theorem isAbelianScheme_of_thickenings_local (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) (hc : IsAdicComplete I R)
    (hc' : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)]
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hY : ∀ e, IsAbelianScheme (Y e))
    (hβ : ∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans R I e) (β e))
    (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left) (hB : IsProjBy B.hom)
    (hs : Smooth B.hom) (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e))
    (hβb : ∀ e, β e ≫ b (e + 1) = b e) :
    ∃ _ : GrpObj B, IsAbelianScheme B ∧ ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e) := by
  have hM : MorAlgSt := GlobalTheory.LN.ega_holds.2.1
  have hpr : IsProper B.hom := isProper_of_isProjBy R B.left B.hom hB
  have hs₂ : Smooth (B ⊗ B).hom := by
    change Smooth (pullback.fst B.hom B.hom ≫ B.hom)
    infer_instance
  obtain ⟨mu, hm⟩ := exists_word hM hI hc hc' hβ hB hb hβb
    (FreeGroup.of true * FreeGroup.of false) (B ⊗ B) (isProjBy_tensor R B B hB hB) hs₂
    (fun i => bif i then fst B B else snd B B)
  obtain ⟨io, hi⟩ := exists_word hM hI hc hc' hβ hB hb hβb
    (FreeGroup.of ())⁻¹ B hB hs (fun _ => 𝟙 B)
  obtain ⟨un, hu⟩ := exists_word hM hI hc hc' hβ hB hb hβb
    (1 : FreeGroup Empty) (𝟙_ _) (isProjBy_id R) (inferInstanceAs (Smooth (𝟙 _))) Empty.elim
  obtain ⟨G, hG, hG'⟩ := exists_grpObj hI (fun e => (hY e).comm) hpr hb mu io un
    (fun e T x y x₀ y₀ hx hy => by
      have := hm e T (lift x₀ y₀) (fun i => bif i then x else y) (fun i => by
        cases i
        · simpa using hy
        · simpa using hx)
      rwa [map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of] at this)
    (fun e T x x₀ hx => by
      have := hi e T x₀ (fun _ => x) (fun _ => by rwa [Category.comp_id])
      rwa [map_inv, FreeGroup.lift_apply_of] at this)
    (fun e T => by
      have := hu e T (toUnit _) Empty.elim (fun i => i.elim)
      rwa [map_one] at this)
  refine ⟨G, ⟨hG, hs, hpr, ?_⟩, hG'⟩
  exact geometricallyConnected_of_quotient R (I ^ (0 + 1)) (by simpa using hI) B hs hB (Y 0) (b 0) (hb 0)
    (hY 0).geomConnected

theorem exists_abelianScheme_of_tower : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsAbelianScheme (Y e)) → (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans R I e) (β e)) → ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → (∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) → RelAmple (Y 0) (N 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (_ : GrpObj B) (M : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left), IsAbelianScheme B ∧ M.IsLB ∧ RelAmple B M ∧ (∀ e, IsGrpPullback (Y e) B (thick R I e) (b e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro R _ _ _ _ I hI hc hc' Y _ β hY hβ N hN hv hA
  choose v hv using hv
  obtain ⟨B, M, b, hB, hs, hM, hA', hb, hβb, hiso⟩ := GlobalTheory.LN.ega_holds.1 R I hI hc hc' Y β N v
    (fun e => isPullback_of_isGrpPullback (hβ e)) (fun e => (hY e).smooth) (fun e => ⟨hN e, hv e⟩) hA
  obtain ⟨G, hG, hG'⟩ :=
    isAbelianScheme_of_thickenings_local R I hI hc hc' Y β hY hβ B b hB hs hb hβb
  exact ⟨B, G, M, b, hG, hM, hA', hG', hβb, hiso⟩

end GlobalTheory.AlgGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingOfIsAbove
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbVarRed

theorem isDiscreteValuationRing_of_isAbove :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
      [IsFractionRing R K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
      (V : ValuationSubring L), IsAbove R K V.toSubring → IsDiscreteValuationRing V := by
  intro R K _ _ _ _ _ _ L _ _ _ V h
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K L := .of_algebraMap_eq fun _ => rfl
  have memV : ∀ a : K, algebraMap K L a ∈ V ↔ a ∈ (algebraMap R K).range := fun a => by
    rw [← h]; rfl
  let W : Subalgebra R L :=
    { V.toSubring with
      algebraMap_mem' := fun r => (memV (algebraMap R K r)).2 ⟨r, rfl⟩ }
  have hVn : IsNoetherianRing V := (GlobalTheory.krullAkizuki K W).1
  have hnf : ¬ IsField V := by
    intro hf
    apply IsDiscreteValuationRing.not_isField R
    have hs : Function.Surjective (algebraMap R K) := fun x => by
      by_cases hx : x = 0
      · exact ⟨0, by simp [hx]⟩
      have hxL : algebraMap K L x ≠ 0 := (map_ne_zero _).2 hx
      have hmem : algebraMap K L x ∈ V := by
        rcases V.mem_or_inv_mem (algebraMap K L x) with h1 | h1
        · exact h1
        · obtain ⟨y, hy⟩ := hf.mul_inv_cancel (a := (⟨_, h1⟩ : V))
            (fun e => inv_ne_zero hxL (congrArg Subtype.val e))
          have hy' : (algebraMap K L x)⁻¹ * (y : L) = 1 := congrArg Subtype.val hy
          have : (y : L) = algebraMap K L x := by
            rw [← inv_inv (algebraMap K L x)]
            exact eq_inv_of_mul_eq_one_right hy'
          exact this ▸ y.2
      exact (memV x).1 hmem
    exact (RingEquiv.ofBijective (algebraMap R K) ⟨IsFractionRing.injective R K, hs⟩).toMulEquiv.isField
      (Field.toIsField K)
  have hval : ValuationRing V := inferInstance
  exact ((IsDiscreteValuationRing.TFAE V hnf).out 1 0).mp hval

end GlobalTheory.AbVarRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormSmulDelSmul
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.SmulForm

theorem loc_smul {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (c : ℂ) (α : A.Fld) (i : A.ι)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : A.loc (c • α) i v = c • A.loc α i v := by
  unfold HolAtlas.loc
  split_ifs
  · rfl
  · exact (smul_zero c).symm

theorem isForm_smul_and_del_smul {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (c : ℂ)
    (α : A.Fld) (h : A.IsForm α) : A.IsForm (c • α) ∧ A.del (c • α) = c • A.del α := by
  have hc (i : A.ι) (S : Finset (Fin (n + n))) : (fun v => (bas n).repr (A.loc (c • α) i v) S) =
      fun v => c • (bas n).repr (A.loc α i v) S := by
    funext v
    rw [loc_smul, map_smul, Finsupp.smul_apply]
  refine ⟨⟨fun i S => ?_, fun x x' e => ?_⟩, funext fun x => ?_⟩
  · rw [hc]
    exact (h.smooth i S).const_smul c
  · rw [Pi.smul_apply, Pi.smul_apply, map_smul, ← h.compat x x' e]
  · have hd (S : Finset (Fin (n + n))) :
        DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
      ((h.smooth x.1.1 S).contDiffAt (x.ch.open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)
    rw [Pi.smul_apply, HolAtlas.del, HolAtlas.del, delAt, delAt, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← mul_smul_comm, coefwise, coefwise, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hc, GlobalTheory.del_const_smul c (hd S), ContinuousLinearMap.smul_apply, smul_assoc]

end GlobalTheory.CxForm.SmulForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagTan

section Comb

open DeRham Cris MonObj

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

def lieComb {n : ℕ} (cf : Fin n → R) (v : Fin n → (epsR R ⟶ A)) : epsR R ⟶ A :=
  (List.ofFn fun i => GrpTangent.epsScale (cf i) ≫ v i).prod

theorem isLieComb_lieComb {n : ℕ} (cf : Fin n → R) (v : Fin n → (epsR R ⟶ A)) : IsLieComb cf v (lieComb cf v) :=
  ⟨_, fun _ => rfl, rfl⟩

theorem rel_lieComb {N : Type*} [AddCommMonoid N] [Module R N] {P : N → (epsR R ⟶ A) → Prop} (h0 : P 0 1)
    (ha : ∀ {f f' v v'}, P f v → P f' v' → P (f + f') (v * v'))
    (hs : ∀ {f v}, P f v → ∀ r : R, P (r • f) (GrpTangent.epsScale r ≫ v)) :
    ∀ {n : ℕ} (cf : Fin n → R) {f : Fin n → N} {v : Fin n → (epsR R ⟶ A)}, (∀ i, P (f i) (v i)) →
      P (∑ i, cf i • f i) (lieComb cf v)
  | 0, _, _, _, _ => by simpa [lieComb] using h0
  | n + 1, cf, f, v, h => by
    rw [Fin.sum_univ_succ, lieComb, List.ofFn_succ, List.prod_cons]
    exact ha (hs (h 0) _) (rel_lieComb h0 ha hs (fun i => cf i.succ) fun i => h i.succ)

theorem isLieImage_lieComb {n : ℕ} (cf : Fin n → R) {f : Fin n → HdR A} {v : Fin n → (epsR R ⟶ A)}
    (h : ∀ i, DeRham.IsLieImage (f i) (v i)) : DeRham.IsLieImage (∑ i, cf i • f i) (lieComb cf v) :=
  rel_lieComb (isLieImage_one_iff.2 (zero_mem _)) IsLieImage.add IsLieImage.smul cf h

theorem isKSValue_lieComb {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left}
    {h : IsGrpPullback A A' (epsRed R) i} {n : ℕ} (cf : Fin n → R) {f : Fin n → HdR A} {v : Fin n → (epsR R ⟶ A)}
    (e : ∀ k, IsKSValue h (f k) (v k)) : IsKSValue h (∑ k, cf k • f k) (lieComb cf v) :=
  rel_lieComb ⟨0, ⟨0, zero_mem _, fun _ => (LinearMap.zero_apply _).trans (by simp)⟩, isLieImage_one_iff.2 (zero_mem _)⟩
    IsKSValue.add IsKSValue.smul cf e

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]

theorem isLieComb_iff_isCombAt {A : Over (Sp K)} [GrpObj A] {x : Sp K ⟶ Xo.X} {π : A.left ⟶ Xo.univ.t.G.left}
    (h : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (cf : Fin n → K) (v : Fin n → (epsR K ⟶ A)) (w : epsR K ⟶ A) :
    IsLieComb cf v w ↔ IsCombAt x (fun i => (v i).left ≫ π) cf (w.left ≫ π) :=
  Chart.comb_push h cf v w

def ksChg (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    (HIx Dw Φ → K) →ₗ[K] (HIx Dw Φ → K) where
  toFun M k := ∑ a', ∑ b', g (conjEmb k.1.1) a' k.2.1 * M ⟨k.1, a', b'⟩ * g k.1.1 b' k.2.2
  map_add' M M' := by ext k; simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' r M := by ext k; simp [Finset.mul_sum, mul_assoc, mul_left_comm]

theorem ksChg_apply (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (M : HIx Dw Φ → K) (k : HIx Dw Φ) :
    ksChg Φ g M k = ∑ a', ∑ b', g (conjEmb k.1.1) a' k.2.1 * M ⟨k.1, a', b'⟩ * g k.1.1 b' k.2.2 := rfl

theorem ksChg_eq_mul (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (M : HIx Dw Φ → K) (τ : Φ) : (Matrix.of fun a b => ksChg Φ g M ⟨τ, a, b⟩) =
      (g (conjEmb τ.1)).transpose * (Matrix.of fun a b => M ⟨τ, a, b⟩) * g τ.1 := by
  ext a b
  simp only [Matrix.of_apply, ksChg_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem ksChg_ksChg (Φ : Finset (E →+* ℂ)) (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (M : HIx Dw Φ → K) : ksChg Φ g (ksChg Φ g' M) = ksChg Φ (fun τ => g' τ * g τ) M := by
  funext ⟨τ, a, b⟩
  have h : (Matrix.of fun a b => ksChg Φ g (ksChg Φ g' M) ⟨τ, a, b⟩) =
      Matrix.of fun a b => ksChg Φ (fun τ => g' τ * g τ) M ⟨τ, a, b⟩ := by
    simp only [ksChg_eq_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  exact congrFun (congrFun h a) b

theorem ksChg_one (Φ : Finset (E →+* ℂ)) (M : HIx Dw Φ → K) : ksChg Φ (fun _ => 1) M = M := by
  funext ⟨τ, a, b⟩
  have h := ksChg_eq_mul Φ (fun _ => 1) M τ
  rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at h
  exact congrFun (congrFun h a) b

theorem exists_frChg_inv {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K} {a : K}
    {y y' : FrPt Xo c K} (h : FrChg g a y y') :
    ∃ g' a', FrChg g' a' y' y ∧ (∀ τ, g' τ * g τ = 1) ∧ ∀ τ, g τ * g' τ = 1 := by
  obtain ⟨g', a', -, h'⟩ := (frChg_exists_unique E H Dw l Xo c K y' y).1 h.1.symm
  have C := frChg_calculus E H Dw l Xo c K
  have e := ((frChg_exists_unique E H Dw l Xo c K y y).2 _ _ _ _ ((C.1 _ _ _ _ _ _ _ h).1 h') (C.2.1 y)).1
  have e' := ((frChg_exists_unique E H Dw l Xo c K y' y').2 _ _ _ _ ((C.1 _ _ _ _ _ _ _ h').1 h) (C.2.1 y')).1
  exact ⟨g', a', h', congrFun e, congrFun e'⟩

theorem smul_sum_smul_sum {N α β γ : Type} [AddCommGroup N] [Module K N] [Fintype α] [Fintype β] [Fintype γ]
    (p : α → K) (M : α → β → K) (q : β → γ → K) (n : γ → N) :
    ∑ a, p a • ∑ b, M a b • ∑ k, q b k • n k = ∑ k, (∑ a, ∑ b, p a * M a b * q b k) • n k := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul, mul_assoc]
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

open DeRham Cris in

theorem IsKS.of_frChg {Φ : Finset (E →+* ℂ)} {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K}
    {a : K} {y y' : FrPt Xo c K} (h : FrChg g a y y') {x' : Sp (DualNumber K) ⟶ Xo.X} {M' : HIx Dw Φ → K}
    (hM : IsKS Φ y' x' M') : IsKS Φ y x' (ksChg Φ g M') := by
  obtain ⟨g', a', h', e, -⟩ := exists_frChg_inv h
  obtain ⟨A, _, A', _, π, π', i, hi, ψ, ub, hb, hπ, hπ', hiπ, hψ, hub, hhb, hrow⟩ := hM
  rw [h.1] at hπ
  obtain ⟨N, _, _, v, -, -, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo K y.x
  choose n hn using fun σ k => (htan _).1 (y.tan σ k)
  have hn' : ∀ σ k, y'.u σ k = v (∑ j, g σ k j • n σ j) := fun σ k => by
    have := h.2.1 σ k
    rwa [show y.u σ = fun j => v (n σ j) from funext fun j => (hn σ j).symm, hcomb] at this
  have key : ∀ {m : ℕ} (cf : Fin m → K) (u : Fin m → (epsR K ⟶ A)) (b : Fin m → N) (w : epsR K ⟶ A),
      (∀ j, (u j).left ≫ π = v (b j)) → (IsLieComb cf u w ↔ w.left ≫ π = v (∑ j, cf j • b j)) :=
    fun cf u b w hu => by rw [isLieComb_iff_isCombAt hπ, funext hu, hcomb]
  have hub' : ∀ σ k, (ub σ k).left ≫ π = v (∑ j, g σ k j • n σ j) := fun σ k => (hub σ k).trans (hn' σ k)
  have hu : ∀ σ k, (lieComb (g' σ k) (ub σ)).left ≫ π = v (n σ k) := fun σ k => by
    rw [(key _ _ _ _ (hub' σ)).1 (isLieComb_lieComb _ _)]
    congr 1
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, e, Matrix.one_apply]
    simp
  refine ⟨A, _, A', _, π, π', i, hi, ψ, fun σ k => lieComb (g' σ k) (ub σ),
    fun q => ∑ j, g' q.1 q.2 j • hb ⟨q.1, j⟩, hπ, hπ', hiπ, hψ, fun σ k => (hu σ k).trans (hn σ k),
    fun σ k => isLieImage_lieComb _ (hhb σ), fun τ a => ?_⟩
  choose w hw f hf hd hv using hrow τ
  refine ⟨lieComb (fun a' => g (conjEmb τ.1) a' a) w, (key _ _ _ _ (hu τ.1)).2 ?_,
    ∑ a', g (conjEmb τ.1) a' a • f a', Submodule.sum_mem _ fun a' _ => Submodule.smul_mem _ _ (hf a'),
    fun ⟨σ, k⟩ => ?_, isKSValue_lieComb _ hv⟩
  · rw [(key _ _ _ _ fun a' => (key _ _ _ _ (hub' τ.1)).1 (hw a')).1 (isLieComb_lieComb _ _)]
    congr 1
    exact smul_sum_smul_sum _ (fun a' b' => M' ⟨τ, a', b'⟩) _ _
  · simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hd, smul_eq_mul]
    by_cases hσ : σ = conjEmb τ.1
    · subst hσ
      have := congrFun (congrFun (e (conjEmb τ.1)) k) a
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    · simp [hσ]

theorem isKS_frChg_iff (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (a : K) (y y' : FrPt Xo c K) (h : FrChg g a y y') (x' : Sp (DualNumber K) ⟶ Xo.X) (M' : HIx Dw Φ → K) :
    IsKS Φ y' x' M' ↔ IsKS Φ y x'
      (fun k => ∑ a', ∑ b', g (conjEmb k.1.1) a' k.2.1 * M' ⟨k.1, a', b'⟩ * g k.1.1 b' k.2.2) := by
  refine ⟨fun k => k.of_frChg h, fun k => ?_⟩
  obtain ⟨g', a', h', -, e⟩ := exists_frChg_inv h
  have := IsKS.of_frChg h' (M' := ksChg Φ g M') k
  rwa [ksChg_ksChg, funext e, ksChg_one] at this

end GlobalTheory.FlagTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfBaseChangeField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefFieldDescent

theorem interNum_one_nonneg_of_isNef {k : Type} [Field k] {V : Scheme.{0}} [Algebra k Γ(V, ⊤)]
    (hp : IsProjOver (strHom k V)) (hd : topologicalKrullDim V ≤ 1) {N : LB V} (hN : IsNef k N) :
    0 ≤ interNum k (GlobalTheory.structureModule V) ![N] := by
  refine CurveDevissage.interNum_one_nonneg hp hd hN.isLB (fun Z i hi hZ _ ha hdZ => ?_) _ inferInstance
  have hpr : IsProper (strHom k V) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  have h := (isNef_iff_isClosedImmersion.1 hN).2 Z i hi hZ hdZ inferInstance
  rw [interNumOn, interNum_pushforward_of_isClosedImmersion ha _ (isLB_vecOne hN.isLB)] at h
  rw [topSelf_def]
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j; rfl

theorem isNef_of_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ L : LB Y, L.IsLB → (letI := algebraΓOfHom q; IsNef E (L.pull π)) → (letI := algebraΓOfHom p; IsNef k L) := by
  intro k E _ _ _ Y X p q π H hp L hL hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  refine ⟨hL, fun C hC => ?_⟩
  have H₁ : IsPullback (pullback.fst (redι C) π) (pullback.snd (redι C) π ≫ q) (redι C ≫ p)
      (spMap (algebraMap k E)) := (IsPullback.of_hasPullback (redι C) π).paste_vert H
  have hpC : IsProjOver (redι C ≫ p) := ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
  have hpr : IsProper (redι C ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hpC).1
  have hp' := ProjSpace.isProjOver_of_isPullback_spMap _ H₁ hpC
  have hd : topologicalKrullDim (pullback (redι C) π : Scheme.{0}) ≤ 1 :=
    (FieldExtDim.topologicalKrullDim_baseChange_le k E _ _ _ _ _ H₁).trans
      ((topologicalKrullDim_red C).trans hC.2).le
  have hLC := LB.isLB_pull hL (redι C)
  have key := FieldChangeInter.interNum_pull H₁ (isLB_vecOne hLC)
  letI := algebraΓOfHom (pullback.snd (redι C) π ≫ q)
  have hN' : IsNef E ((L.pull π).pull (pullback.snd (redι C) π)) :=
    hN.pull_of_isClosedImmersion _ fun _ => rfl
  have h0 := interNum_one_nonneg_of_isNef (k := E)
    (by rw [strHom_eq (f := pullback.snd (redι C) π ≫ q) fun _ => rfl]; exact hp') hd hN'
  rw [interNumRed_one_eq hL]
  refine (h0.trans_eq ?_).trans_eq key
  refine interNum_congr_cls E _ (isLB_vecOne hN'.isLB)
    (fun i => LB.isLB_pull (isLB_vecOne hLC i) _) fun i => ?_
  fin_cases i
  change pull _ (pull π (cls L hL)) = pull _ (pull (redι C) (cls L hL))
  simp only [← pull_comp, pullback.condition]

end GlobalTheory.NefFieldDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn
section
set_option autoImplicit false

noncomputable section

open Set Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm
open GlobalTheory.GoodMetric (coordVec)
open Filter Topology
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm

def ofValuesTwo {n : ℕ} (Ψ : V n → V n → V n → V n → ℂ) : Ev n :=
  (1 / 4 : ℂ) • ∑ a, ∑ b, ∑ c, ∑ d,
    Ψ (coordVec a) (coordVec b) (coordVec c) (coordVec d) • (sym (a, b) * sym (c, d))

variable {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n}

def midIn (T : HermSeq A 1 1) (a : T.κ) (i : A.ι) (v : V n) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  T.mid a ((A.e i).symm v)

def subIn (T : HermSeq A 1 1) (a : T.κ) (i : A.ι) (v : V n) : Matrix (Fin 1) (Fin 1) ℂ :=
  T.sub a ((A.e i).symm v)

def quotIn (T : HermSeq A 1 1) (a : T.κ) (i : A.ι) (v : V n) : Matrix (Fin 1) (Fin 1) ℂ :=
  T.quot a ((A.e i).symm v)

def potS (T : HermSeq A 1 1) (a : T.κ) (y : M) : ℝ :=
  Real.log ((T.sub a y 0 0).re / (T.mid a y (.inl 0) (.inl 0)).re)

def potQ (T : HermSeq A 1 1) (a : T.κ) (y : M) : ℝ :=
  Real.log ((T.quot a y 0 0).re / (quotGram (T.mid a y) 0 0).re)

def locForm (T : HermSeq A 1 1) (a : T.κ) (i : A.ι) (v ξ η : V n) : ℂ :=
  extTrace (midIn T a i) v ξ η + (potS T a ((A.e i).symm v) : ℂ) * chernOne (quotIn T a i) v ξ η +
    (potQ T a ((A.e i).symm v) : ℂ) * chernOne (fun w => subGram (midIn T a i w)) v ξ η

def frm (T : HermSeq A 1 1) (y : M) : T.κ := (T.cover y).choose

def secForm (T : HermSeq A 1 1) : A.Fld := fun x => (ofValues (locForm T (frm T x.pt) x.1.1 x.crd) : Alt n)

variable (T : HermSeq A 1 1) (a b : T.κ) (i : A.ι)

def chartSet : Set (V n) := (A.e i).target ∩ (A.e i).symm ⁻¹' T.U a

def gIn (v : V n) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := T.g a b ((A.e i).symm v)

theorem isOpen_chartSet : IsOpen (chartSet T a i) := (A.e i).isOpen_inter_preimage_symm (T.isOpen a)

theorem isPosFrame_midIn : IsPosFrame (chartSet T a i) (midIn T a i) :=
  ⟨isOpen_chartSet T a i, fun p q => (T.smooth a).2.1 p q i, fun _ hv => (T.posDef a _ hv.2).2.1⟩

theorem holo_gIn {v : V n} (hv : v ∈ chartSet T a i ∩ chartSet T b i) :
    MContDiffAt ∞ (gIn T a b i) v ∧ ∀ᶠ w in 𝓝 v, ∀ η, mdbar (gIn T a b i) w η = 0 := by
  have hs : chartSet T a i ∩ chartSet T b i = (A.e i).target ∩ (A.e i).symm ⁻¹' (T.U a ∩ T.U b) := by
    ext w; simp only [chartSet, mem_inter_iff, mem_preimage]; tauto
  have ho : IsOpen (chartSet T a i ∩ chartSet T b i) := (isOpen_chartSet T a i).inter (isOpen_chartSet T b i)
  have hd : ∀ p q, DifferentiableOn ℂ (fun w => gIn T a b i w p q) (chartSet T a i ∩ chartSet T b i) := by
    intro p q; rw [hs]; exact T.holo a b p q i
  refine ⟨fun p q => ?_, ?_⟩
  · have h1 : ContDiffOn ℂ ∞ (fun w => gIn T a b i w p q) (chartSet T a i ∩ chartSet T b i) :=
      ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ ho (hd p q)
    exact (h1.restrict_scalars ℝ).contDiffAt (ho.mem_nhds hv)
  filter_upwards [ho.mem_nhds hv] with w hw η
  ext p q
  rw [mdbar_apply, dbar_eq_zero ((hd p q).differentiableAt (ho.mem_nhds hw))]
  rfl

theorem trans_eventually {v : V n} (hv : v ∈ chartSet T a i ∩ chartSet T b i) :
    ∀ᶠ w in 𝓝 v, w ∈ chartSet T a i ∩ chartSet T b i ∧
      subIn T b i w = chg (gIn T a b i w).toBlocks₁₁ (subIn T a i w) ∧
      midIn T b i w = chg (gIn T a b i w) (midIn T a i w) ∧
      quotIn T b i w = chg (gIn T a b i w).toBlocks₂₂ (quotIn T a i w) ∧
      (gIn T a b i w).toBlocks₂₁ = 0 := by
  have ho : IsOpen (chartSet T a i ∩ chartSet T b i) := (isOpen_chartSet T a i).inter (isOpen_chartSet T b i)
  filter_upwards [ho.mem_nhds hv] with w hw
  have h := T.trans a b _ ⟨hw.1.2, hw.2.2⟩
  exact ⟨hw, h.1, h.2.1, h.2.2, T.tri a b _ ⟨hw.1.2, hw.2.2⟩⟩

end GlobalTheory.SecForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingHyperbolicFirstStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_hyperbolic_first : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∃ R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E, frame H * R = 1 ∧ R * frame H = 1 := by
  first | exact @GlobalTheory.LeviHC.FrameInv.frame_invertible | exact GlobalTheory.LeviHC.FrameInv.frame_invertible | (intros; apply GlobalTheory.LeviHC.FrameInv.frame_invertible <;> assumption)
end

