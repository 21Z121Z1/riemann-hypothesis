import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0053
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0054
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogeneousFormNonvanishingPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticeBasisExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HcptPull

theorem dual_pull : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (ω : Submodule R (Module.Dual Ω V)) (ω' : Submodule R' (Module.Dual Ω' V')) (r : ℕ) (b : Fin r → Module.Dual Ω W), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (0 < r → ω' = Submodule.span R' (jd '' (ω : Set (Module.Dual Ω V)))) → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = ⊤ → ω.map (W.dualRestrict.restrictScalars R) = Submodule.span R (Set.range b) → Submodule.span R' {e | e ∈ W' ∧ ∀ w ∈ ω', w e ∈ R'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} : Set V)) := by
  intro Ω Ω' _ _ i R R' V V' _ _ _ _ j jd W W' ω ω' r b hj hR hjd hW' hω' hli hsp hmap
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hD : ∀ f : Module.Dual Ω W, f = 0 := by
      intro f
      have hf : f ∈ Submodule.span Ω (Set.range b) := hsp ▸ Submodule.mem_top
      rw [Set.range_eq_empty, Submodule.span_empty] at hf
      exact (Submodule.mem_bot Ω).1 hf
    have hW0 : ∀ e ∈ W, e = 0 := by
      intro e he
      have : (⟨e, he⟩ : W) = 0 :=
        (Module.forall_dual_apply_eq_zero_iff Ω _).1 fun f => by rw [hD f]; rfl
      exact congrArg Subtype.val this
    have hW'0 : W' = ⊥ := by
      rw [hW', Submodule.span_eq_bot]
      rintro _ ⟨e, he, rfl⟩
      rw [hW0 e he, map_zero]
    have hS0 : Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} = ⊥ :=
      Submodule.span_eq_bot.2 fun e he => hW0 e he.1
    rw [hS0, Submodule.span_eq_bot.2, Submodule.span_eq_bot.2]
    · rintro _ ⟨e, he, rfl⟩
      have : e = 0 := by simpa using he
      rw [this, map_zero]
    · rintro e ⟨he, -⟩
      rw [hW'0] at he
      exact (Submodule.mem_bot Ω').1 he
  have hω'' := hω' hr
  let hb : Module.Basis (Fin r) Ω (Module.Dual Ω W) := Module.Basis.mk hli hsp.ge
  have hbb : ∀ k, hb k = b k := fun k => Module.Basis.mk_apply hli hsp.ge k
  haveI : Module.Finite Ω (Module.Dual Ω W) := Module.Finite.of_basis hb
  haveI : Module.Finite Ω W := Module.finite_dual_iff Ω |>.1 inferInstance
  let c : Module.Basis (Fin r) Ω W := hb.dualBasis.map (Module.evalEquiv Ω W).symm
  have hbc : ∀ l k, b l (c k) = if l = k then 1 else 0 := by
    intro l k
    have h1 : c k = (Module.evalEquiv Ω W).symm (hb.dualBasis k) := by
      simp [c]
    rw [h1, Module.apply_evalEquiv_symm_apply, ← hbb, Module.Basis.dualBasis_apply_self]

  have hexp : ∀ e : W, e = ∑ k, b k e • c k := by
    intro e
    conv_lhs => rw [← c.sum_repr e]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have : b k e = ∑ m, c.repr e m * b k (c m) := by
      calc b k e = b k (∑ m, c.repr e m • c m) := by rw [c.sum_repr]
        _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
    rw [this]
    simp [hbc]

  have hcS : ∀ k, (c k : V) ∈ {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} := by
    intro k
    refine ⟨(c k).2, fun w hw => ?_⟩
    have hwr : W.dualRestrict w ∈ Submodule.span R (Set.range b) := by
      rw [← hmap]
      exact ⟨w, hw, rfl⟩
    have key : ∀ f ∈ Submodule.span R (Set.range b), f (c k) ∈ R := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        rw [hbc]
        split_ifs
        · exact R.one_mem
        · exact R.zero_mem
      | zero => simpa using R.zero_mem
      | add x y _ _ hx hy => simpa using R.add_mem hx hy
      | smul a x _ hx =>
        have : (a • x) (c k) = (a : Ω) * x (c k) := rfl
        rw [this]
        exact R.mul_mem a.2 hx
    exact key _ hwr

  have hpick : ∀ l, ∃ w ∈ ω, W.dualRestrict w = b l := by
    intro l
    have : b l ∈ ω.map (W.dualRestrict.restrictScalars R) := by
      rw [hmap]
      exact Submodule.subset_span ⟨l, rfl⟩
    obtain ⟨w, hw, hwb⟩ := this
    exact ⟨w, hw, hwb⟩
  choose wl hwl hwb using hpick
  have hspan : ∀ e' ∈ W', ∃ a : Fin r → Ω', e' = ∑ k, a k • j (c k : V) := by
    intro e' he'
    have hle : W' ≤ Submodule.span Ω' (Set.range fun k => j (c k : V)) := by
      rw [hW', Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      have h1 : e = ∑ k, b k ⟨e, he⟩ • (c k : V) := by
        have := congrArg (Subtype.val) (hexp ⟨e, he⟩)
        simpa using this
      rw [SetLike.mem_coe, h1, map_sum]
      refine sum_mem fun k _ => ?_
      rw [hj.1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω').1 (hle he')
    exact ⟨a, ha.symm⟩
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro e' ⟨he', hint⟩
    obtain ⟨a, rfl⟩ := hspan e' he'
    have hal : ∀ l, a l ∈ R' := by
      intro l
      have h1 := hint (jd (wl l)) (by
        rw [hω'']
        exact Submodule.subset_span ⟨wl l, hwl l, rfl⟩)
      have h2 : jd (wl l) (∑ k, a k • j (c k : V)) = a l := by
        rw [map_sum]
        have : ∀ k, jd (wl l) (a k • j (c k : V)) = a k * (if l = k then 1 else 0) := by
          intro k
          have h3 : wl l (c k : V) = if l = k then 1 else 0 := by
            rw [← hbc, ← hwb]
            simp [Submodule.dualRestrict_apply]
          rw [map_smul, hjd, smul_eq_mul, h3, apply_ite i, map_one, map_zero]
        simp [this]
      rwa [h2] at h1
    rw [SetLike.mem_coe]
    refine sum_mem fun k _ => ?_
    have : a k • j (c k : V) = (⟨a k, hal k⟩ : R') • j (c k : V) := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨(c k : V), Submodule.subset_span (hcS k), rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨?_, fun w hw => ?_⟩
      · rw [hW']
        exact Submodule.subset_span ⟨x, hx.1, rfl⟩
      · rw [hω''] at hw
        induction hw using Submodule.span_induction with
        | mem f hf =>
          obtain ⟨u, hu, rfl⟩ := hf
          rw [hjd]
          exact hR _ (hx.2 u hu)
        | zero => simpa using R'.zero_mem
        | add f g _ _ hf hg => simpa using R'.add_mem hf hg
        | smul a f _ hf =>
          have : (a • f) (j x) = (a : Ω') * f (j x) := rfl
          rw [this]
          exact R'.mul_mem a.2 hf
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx =>
      have : j (a • x) = (⟨i a, hR a a.2⟩ : R') • j x := hj.1 (a : Ω) x
      rw [this]
      exact Submodule.smul_mem _ _ hx

end GlobalTheory.CompanionTheory.Ar.HcptPull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualRevDualRev
section
namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {K : Type} {ι : K → Type} {R : Type} [CommRing R]

def dualRev {r : ℕ} (Q : LocPair ι R (Fin r)) : LocPair ι R (Fin r) :=
  ⟨fun i => -Q.x (Fin.rev i), fun i => -Q.x' (Fin.rev i), fun i => Q.g (Fin.rev i), fun i => Q.f (Fin.rev i)⟩

def labelPair (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (labelRk D s))
  | .inl τ => T.comp fun i => (τ, Fin.castAdd D.q i)
  | .inr τ => dualRev (T.comp fun i => (τ, Fin.natAdd D.p i))

def omPair (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (labelRk D s.swap)) :=
  fun s => dualRev (labelPair D T s.swap)

def omPairM (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (Sum.elim (fun _ : CMType H => D.q) (fun _ : CMType H => D.p) s))
  | .inl τ => omPair D T (.inl τ)
  | .inr τ => omPair D T (.inr τ)

theorem dualRev_dualRev {r : ℕ} (Q : LocPair ι R (Fin r)) : dualRev (dualRev Q) = Q := by
  obtain ⟨x, x', f, g⟩ := Q
  simp [dualRev, Fin.rev_rev]

theorem map_map {R' R'' : Type} [CommRing R'] [CommRing R''] {σ : Type} (T : LocPair ι R σ) (ψ : R →+* R')
    (ψ' : R' →+* R'') : (T.map ψ).map ψ' = T.map (ψ'.comp ψ) := by
  obtain ⟨x, x', f, g⟩ := T
  simp [LocPair.map, MvPolynomial.map_map]

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EmbeddingBaseChangeCompat
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem isEmb_baseChange_square : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ (A : Subalgebra R (T → R)) (A' : Subalgebra R' (T → R')) (ψ : A →+* A'), (∀ (a : A) t, (ψ a).1 t = algebraMap R R' (a.1 t)) → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)) (j' : Γ'.G.left ⟶ Spec (CommRingCat.of A')), Γ.IsEmb A j → Γ'.IsEmb A' j' → F ≫ j = j' ≫ Spec.map (CommRingCat.ofHom ψ) :=
  PositivityTheory.HtPt.Mh.emb_square

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbedding
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem exists_unique_emb_btOrder_top : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), ∃! j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)), Γ.IsEmb (Γ.btOrder ⊤) j :=
  @PositivityTheory.HtPt.Mh.emb

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMapStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_dominating_map : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (o' : Type) [CommRing o'] (Ω' : Type) [Field Ω'] [Algebra o' Ω'] (κ' : Type) [Finite κ'] (y : κ' → Ω') (M' : PModel o' y) (i : Ω →+* Ω'), (∀ p', p' ∈ ctrSet o x i M'.ξ) → ∃! f : M'.X ⟶ M.X, Dominates M'.ξ M.ξ f i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates | exact GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates | (intros; apply GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreCurveDegreeCompareStatement
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_curve_degree_compare : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → ∃ Y : Crv.CurveIn Γ.C Γ.η, Y.x = Γ.z ∧ ∀ (L : Lat ξ Ω) (n : ℤ), L.IsVB 1 ⊤ → (Γ.HasDeg L n ↔ Y.IsDeg L n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.fibreCurve_curveIn_degree | exact GlobalTheory.CompanionTheory.Ar.Flat.fibreCurve_curveIn_degree | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.fibreCurve_curveIn_degree <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatricesRegularGeneric
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem exists_cell {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) F) (N : Matrix (Fin r) (Fin n) F) (hA : ∀ a b, A a b ∈ O)
    (hN : ∀ a b, N a b ∈ O) (hNA : N * A = 1) (Y : Matrix (Fin r) (Fin r) F)
    (hs : ∀ i : Fin r, ∃ J, NormAt O (A * Y) ((i : ℕ) + 1) i.2 J) :
    ∃ w : Equiv.Perm (Fin r), ∀ (k : ℕ) (hk : k ≤ r), NormAt O Y k hk (w ∘ Fin.castLE hk) := by
  refine GlobalTheory.T.exists_perm_normalized_minors O Y (fun k hk I' I => GlobalTheory.T.normalized_minor_extends O Y k hk I' I) fun k hk => ?_
  cases k with
  | zero => exact ⟨Fin.elim0, normAt_zero O Y _⟩
  | succ k =>
    obtain ⟨J, hJ⟩ := hs ⟨k, hk⟩
    exact exists_normAt O A N hA hN hNA Y _ hk J hJ

theorem big_cell_smooth : ∀ (Ω : Type) [Field Ω] (S : Type) [Fintype S] (r n : S → ℕ) (R : Subring Ω) (O : Subring (GenField Ω r)) [IsLocalRing O] (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (N : ∀ s, Matrix (Fin (r s)) (Fin (n s)) Ω) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), (∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ O) → (∀ s, (T s).det ≠ 0) → (∀ s j l, M s j l ∈ R) → (∀ s l j, N s l j ∈ R) → (∀ s, N s * M s = 1) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → (∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ O) → ∃ t ∈ ratioRing R (flagB M T) J, t ≠ 0 ∧ t ∈ O ∧ t⁻¹ ∈ O ∧ ∃ h : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ locSub (ratioRing R (flagB M T) J) t, (((algebraMap Ω (GenField Ω r)).comp R.subtype).codRestrict (locSub (ratioRing R (flagB M T) J) t) (fun a => h a a.2)).Smooth := by
  intro Ω _ S _ r n R O _ T M N J hRO hT hM hN hNM hJ0 hJr
  classical
  haveI : Finite (GenIx r) := by unfold GenIx; infer_instance
  set i := algebraMap Ω (GenField Ω r) with hi
  set A := ratioRing R (flagB M T) J with hAdef
  let Y : ∀ s, Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := fun s => (T s).map i * genU Ω r s
  let Am : ∀ s, Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) := fun s => (M s).map i
  let Nm : ∀ s, Matrix (Fin (r s)) (Fin (n s)) (GenField Ω r) := fun s => (N s).map i
  have hB : ∀ s, flagB M T s = Am s * Y s := fun s => by
    show (M s * T s).map i * genU Ω r s = (M s).map i * ((T s).map i * genU Ω r s)
    rw [Matrix.map_mul, Matrix.mul_assoc]
  have hNA : ∀ s, Nm s * Am s = 1 := fun s => by
    show (N s).map i * (M s).map i = 1
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hYN : ∀ s, Nm s * flagB M T s = Y s := fun s => by
    rw [hB, ← Matrix.mul_assoc, hNA, Matrix.one_mul]
  have hAmO : ∀ s a b, Am s a b ∈ O := fun s a b => hRO _ (hM _ _ _)
  have hNmO : ∀ s a b, Nm s a b ∈ O := fun s a b => hRO _ (hN _ _ _)

  have hw : ∀ s, ∃ w : Equiv.Perm (Fin (r s)), ∀ (k : ℕ) (hk : k ≤ r s),
      NormAt O (Y s) k hk (w ∘ Fin.castLE hk) := fun s =>
    exists_cell O (Am s) (Nm s) (hAmO s) (hNmO s) (hNA s) (Y s) fun i' => by
      refine ⟨J ⟨s, i'⟩, ?_⟩
      rw [← hB]
      exact ⟨hJ0 ⟨s, i'⟩, hJr ⟨s, i'⟩⟩
  choose w hw using hw
  have hlu := fun s => GlobalTheory.T.lu_decomposition_of_minors ((Y s).submatrix (w s) id) fun k hk => (hw s k hk).1
  choose C V hC hV0 hV1 hCV using hlu

  let v : GenIx r → GenField Ω r := fun q => V q.1 q.2.1.1 q.2.1.2
  set B := Subring.closure (((R.map i : Subring _) : Set (GenField Ω r)) ∪ Set.range v) with hBdef
  have hRB : ∀ a ∈ R, i a ∈ B := fun a ha =>
    Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)
  have hRA : ∀ a ∈ R, i a ∈ A := fun a ha =>
    Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)
  have hVB : ∀ s l k, V s l k ∈ B := fun s l k => by
    rcases lt_trichotomy l k with h | h | h
    · rw [hV0 s l k h]; exact B.zero_mem
    · rw [h, hV1]; exact B.one_mem
    · exact Subring.subset_closure (Or.inr ⟨⟨s, ⟨(l, k), h⟩⟩, rfl⟩)

  let y0 : (q : Σ s, Fin (r s)) → GenField Ω r := fun q =>
    kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 (w q.1 ∘ Fin.castLE q.2.2)
  have hy0 : ∀ q, y0 q ≠ 0 := fun q => (hw q.1 _ q.2.2).1
  have hrat : ∀ (s : S) (k : ℕ) (hk : k ≤ r s) (I : Fin k → Fin (r s)),
      kMinor (Y s) k hk (w s ∘ I) / kMinor (Y s) k hk (w s ∘ Fin.castLE hk) = kMinor (V s) k hk I :=
    fun s k hk I => ratio_eq_kMinor ((Y s).submatrix (w s) id) (C s) (V s) (hC s) (hV0 s) (hV1 s) (hCV s) k hk I
      (hw s k hk).1
  have hyB : ∀ (q : Σ s, Fin (r s)) I, kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 I / y0 q ∈ B := fun q I => by
    have e : I = w q.1 ∘ ((w q.1).symm ∘ I) := by
      ext a; simp
    rw [e]
    show kMinor (Y q.1) _ q.2.2 _ / kMinor (Y q.1) _ q.2.2 _ ∈ B
    rw [hrat]
    exact kMinor_mem B _ (hVB q.1) _ _ _
  have hPB : ∀ (q : Σ s, Fin (r s)) J', stepMinor (flagB M T q.1) q.2 J' / y0 q ∈ B := fun q J' => by
    rw [hB, stepMinor_eq_kMinor]
    exact kMinor_mul_div_mem B (Am q.1) (Y q.1) _ q.2.2 _ (fun a b => hRB _ (hM _ _ _)) (hyB q) J'
  have hPA : ∀ (q : Σ s, Fin (r s)) J', stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ A :=
    fun q J' => Subring.subset_closure (Or.inr ⟨q, J', rfl⟩)
  have hyA : ∀ (q : Σ s, Fin (r s)) I, kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 I /
      stepMinor (flagB M T q.1) q.2 (J q) ∈ A := fun q I => by
    rw [← hYN q.1]
    exact kMinor_mul_div_mem A (Nm q.1) (flagB M T q.1) _ q.2.2 _ (fun a b => hRA _ (hN _ _ _)) (hPA q) I
  have hAO : A ≤ O := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, J', rfl⟩)
    · exact hRO b hb
    · exact hJr q J'

  let tq : (Σ s, Fin (r s)) → GenField Ω r := fun q => y0 q / stepMinor (flagB M T q.1) q.2 (J q)
  have htq0 : ∀ q, tq q ≠ 0 := fun q => div_ne_zero (hy0 q) (hJ0 q)
  have htqA : ∀ q, tq q ∈ A := fun q => hyA q _
  have htqB : ∀ q, (tq q)⁻¹ ∈ B := fun q => by
    show (y0 q / _)⁻¹ ∈ B
    rw [inv_div]
    exact hPB q _
  have htqO : ∀ q, (tq q)⁻¹ ∈ O := fun q => by
    show (y0 q / _)⁻¹ ∈ O
    rw [inv_div, hB, stepMinor_eq_kMinor]
    exact kMinor_mul_div_mem O (Am q.1) (Y q.1) _ q.2.2 _ (hAmO q.1) (hw q.1 _ q.2.2).2 _
  have hAB : A ≤ Subring.closure ((B : Set (GenField Ω r)) ∪ Set.range tq) := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, J', rfl⟩)
    · exact Subring.subset_closure (Or.inl (hRB b hb))
    · have e : stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) =
          (stepMinor (flagB M T q.1) q.2 J' / y0 q) * tq q := by
        show _ = _ * (y0 q / _)
        have := hy0 q
        have := hJ0 q
        field_simp
      rw [SetLike.mem_coe, e]
      exact mul_mem (Subring.subset_closure (Or.inl (hPB q J'))) (Subring.subset_closure (Or.inr ⟨q, rfl⟩))
  have hBA : B ≤ Subring.closure ((A : Set (GenField Ω r)) ∪ Set.range fun q => (tq q)⁻¹) := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, rfl⟩)
    · exact Subring.subset_closure (Or.inl (hRA b hb))
    · obtain ⟨s, ⟨⟨l, k⟩, hlk⟩⟩ := q
      have hlk' : k < l := hlk
      have e1 : V s l k = kMinor (Y s) ((k : ℕ) + 1) k.2 (w s ∘ lastRow k l) / y0 ⟨s, k⟩ := by
        rw [← kMinor_lower_lastRow (V s) (hV0 s) (hV1 s) k l hlk', ← hrat]
      have e2 : V s l k = (kMinor (Y s) ((k : ℕ) + 1) k.2 (w s ∘ lastRow k l) /
          stepMinor (flagB M T s) k (J ⟨s, k⟩)) * (tq ⟨s, k⟩)⁻¹ := by
        rw [e1]
        show _ = _ * (y0 ⟨s, k⟩ / _)⁻¹
        have := hy0 ⟨s, k⟩
        have := hJ0 ⟨s, k⟩
        field_simp
      show V s l k ∈ _
      rw [e2]
      exact mul_mem (Subring.subset_closure (Or.inl (hyA ⟨s, k⟩ _))) (Subring.subset_closure (Or.inr ⟨_, rfl⟩))

  have hv : AlgebraicIndependent Ω v := by
    refine GlobalTheory.T.algebraic_independent_of_adjoin _ v (genU_indep Ω r) fun q => ?_
    rw [← genU_gen]
    have hmem : ∀ s l k, V s l k ∈ IntermediateField.adjoin Ω (Set.range v) := fun s l k => by
      rcases lt_trichotomy l k with h | h | h
      · rw [hV0 s l k h]; exact zero_mem _
      · rw [h, hV1]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, ⟨(l, k), h⟩⟩, rfl⟩
    refine entries_mem _ ((T q.1).submatrix (w q.1) id) ?_ (genU Ω r q.1) (C q.1) (V q.1)
      (genU_zero Ω r q.1) (genU_one Ω r q.1) (hC q.1) (hV0 q.1) (hV1 q.1) ?_ (hmem q.1) _ _ q.2.2
    · rw [Matrix.det_permute]
      exact mul_ne_zero (by rcases Int.units_eq_one_or (Equiv.Perm.sign (w q.1)) with h | h <;> simp [h]) (hT _)
    · rw [← hCV q.1]
      congr 1

  have hL := GlobalTheory.T.localization_closure_equal A B tq htq0 htqA htqB hAB hBA
  have htA : (∏ q, tq q) ∈ A := A.prod_mem fun q _ => htqA q
  have hinv : (∏ q, tq q)⁻¹ = ∏ q, (tq q)⁻¹ := (Finset.prod_inv_distrib _).symm
  refine ⟨∏ q, tq q, htA, Finset.prod_ne_zero_iff.2 fun q _ => htq0 q, hAO htA, ?_, ?_⟩
  · rw [hinv]
    exact O.prod_mem fun q _ => htqO q
  have hR : ∀ a ∈ R, i a ∈ locSub A (∏ q, tq q) := fun a ha => le_locSub _ _ (hRA a ha)
  refine ⟨hR, ?_⟩
  have gen : ∀ (L : Subring (GenField Ω r)), L = locSub B (∏ q, tq q)⁻¹ → ∀ h : ∀ a ∈ R, i a ∈ L,
      ((i.comp R.subtype).codRestrict L (fun a => h a a.2)).Smooth := by
    rintro _ rfl h
    refine GlobalTheory.T.localization_closure_smooth R v hv _ ?_ (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun q _ => htq0 q)) h
    rw [hinv]
    exact B.prod_mem fun q _ => htqB q
  exact gen _ hL hR

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeSpanIndependentStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_span_independent : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (u : Fin r → V × Module.Dual Ω V), (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → (𝓗.quot σ).IsVB r (HT.eigSp 𝓗.ρH σ) ∧ (detLat (𝓗.quot σ) u).IsVB 1 ⊤ ∧ ∀ (p : Cpt ξ) (A : Matrix (Fin r) (Fin r) Ω), (𝓗.quot σ).IsFrameAt (fun i => ∑ j, A i j • u j) p → (detLat (𝓗.quot σ) u).IsGenAt p A.det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.HodgeLat.quot_det_bundle | exact GlobalTheory.CompanionTheory.Ar.Flat.HodgeLat.quot_det_bundle | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.HodgeLat.quot_det_bundle <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogeneousFormNonvanishingPointStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_form_nonvanishing_point : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (r : ℕ) (x' : Fin (r + 1) → Ω) (hG : Gz.IsHomogeneous (d + 1)) (h0 : aeval (fun j => ∏ k, y ⟨k, E j k⟩) Gz ≠ 0) (hβ : ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0) (hx' : x' ≠ 0) (hF : ∀ i l, x' l ≠ 0 → x' i / x' l ∈ blockFnField y) (hch : ∀ a l, (∏ k, y ⟨k, E a k⟩) ≠ 0 → x' l ≠ 0 → SncChart (Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪ Set.range (fun k => x' k / x' l))) e (aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz))), ∃ (y' : (Σ _ : Unit, Fin (r + 1)) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin (r + 1)))), (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧ ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧ ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) β) = 0 → z ∈ mcPts J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.final_data_main | exact GlobalTheory.CompanionTheory.Ar.SegreChart.final_data_main | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.final_data_main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegular
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.IntReg

theorem mem_regAt_of_isIntegral_of_stalk :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ), IsCptGen ξ →
      IsIntegrallyClosed (X.presheaf.stalk p.1) → ∀ a : Ω, IsIntegral ℤ a → a ∈ regAt ξ p := by
  intro X Ω _ ξ p hξ hcl a ha
  have hinj : Function.Injective (genMap ξ p) := hξ.inj p
  let _ : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hmap : ∀ x, algebraMap (X.presheaf.stalk p.1) Ω x = genMap ξ p x := fun _ => rfl
  have : IsDomain (X.presheaf.stalk p.1) := hinj.isDomain _
  have : FaithfulSMul (X.presheaf.stalk p.1) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨b, c, hc, e⟩ := exists_frac_genMap ξ hξ p z
    exact ⟨b, c, by rw [hmap, hmap, ← e, mul_div_cancel_right₀ _ hc]⟩
  have hb : _root_.IsIntegral (X.presheaf.stalk p.1) a := ha.tower_top
  obtain ⟨w, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb
  exact ⟨w, rfl⟩

end GlobalTheory.CompanionTheory.Ar.IntReg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

def IsOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type}
    [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ)
    (p : Sp ℂ ⟶ Xo.X) : Prop :=
  ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ Y.j = z ≫ 𝔐.f ∧ x ≫ pullback.fst _ _ = p ∧ x ≫ pullback.snd _ _ = spMap κ

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleNormalProperPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_normal_proper_pullback : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') [IsProper f], Dominates ξ' ξ f i → Function.Bijective i → IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p' : Cpt ξ', f p'.1 ⤳ p.1 → (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t)) → L.IsGenAt p t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.lat_isGenAt_of_proper_birational | exact GlobalTheory.CompanionTheory.Ar.Flat.lat_isGenAt_of_proper_birational | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.lat_isGenAt_of_proper_birational <;> assumption)
end

