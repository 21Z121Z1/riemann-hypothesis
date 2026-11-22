import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1297
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRegularSequenceOfCommonZeros
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore GlobalTheory.QCoh RingTheory.Sequence

namespace GlobalTheory.RegBasis

section General

variable {X : Scheme.{0}} {L : LB X} {k : Type} [Field k] [Algebra k Γ(X, ⊤)] {V : Type} [AddCommGroup V]
  [Module k V] (φ : V →ₛₗ[algebraMap k Γ(X, ⊤)] L.Sec)

def vanishAt (x : X) : Submodule k V where
  carrier := {w | x ∉ nonzeroLocus (φ w)}
  add_mem' := fun {a b} ha hb hx => by
    rw [map_add] at hx
    exact (nonzeroLocus_add_le _ _ hx).elim ha hb
  zero_mem' := fun hx => by
    rw [map_zero] at hx
    exact nonzeroLocus_secZero.le hx
  smul_mem' := fun c a ha hx => by
    rw [φ.map_smulₛₗ] at hx
    exact ha ((nonzeroLocus_secScale _ _).le hx).2

theorem vanishAt_eq_top {ι : Type} {v : ι → V} (hv : Submodule.span k (Set.range v) = ⊤) {x : X}
    (hx : ∀ i, x ∉ nonzeroLocus (φ (v i))) : vanishAt φ x = ⊤ :=
  top_le_iff.1 (hv.ge.trans (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hx i)))

theorem exists_regSeq [Infinite k] [Module.Finite k V] [AlgebraicGeometry.IsNoetherian X] (hL : L.IsLB)
    (c : X → L.ι) (hc : ∀ x, x ∈ L.U (c x)) (m : ℕ) (F : X.Modules) [IsFiniteQC F] (W : Submodule k V)
    (hW : Module.finrank k W + m = Module.finrank k V)
    (h : ∀ v : Fin m → V, W ⊔ Submodule.span k (Set.range v) = ⊤ → ∀ x, vanishAt φ x = ⊤ →
      IsWeaklyRegular (F.presheaf.stalk x :) (List.ofFn fun i => X.presheaf.germ _ x (hc x) ((φ (v i)).f (c x)))) :
    ∃ v : Fin m → V, W ⊔ Submodule.span k (Set.range v) = ⊤ ∧ RegSeq hL F (List.ofFn fun i => φ (v i)) := by
  induction m generalizing F W with
  | zero =>
    refine ⟨Fin.elim0, ?_, by rw [List.ofFn_zero]; trivial⟩
    rw [Submodule.eq_top_of_finrank_eq hW, top_sup_eq]
  | succ m ih =>
    have hne : W ≠ ⊤ := fun e => by
      rw [e, finrank_top] at hW
      omega
    have : Finite {x : X // x ∈ assPoints F ∧ vanishAt φ x ≠ ⊤} :=
      ((finite_assPoints F).subset fun _ hx => hx.1).to_subtype
    obtain ⟨w, hw⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
      (fun o : Option {x : X // x ∈ assPoints F ∧ vanishAt φ x ≠ ⊤} => o.elim W fun x => vanishAt φ x.1)
      (by
        rintro (_ | x)
        exacts [hne, x.2.2])
    have hsup : ∀ v : Fin m → V, W ⊔ Submodule.span k {w} ⊔ Submodule.span k (Set.range v) =
        W ⊔ Submodule.span k (Set.range (Fin.cons w v : Fin (m + 1) → V)) := fun v => by
      rw [Fin.range_cons, Submodule.span_insert, sup_assoc]
    have key : ∀ v : Fin m → V, W ⊔ Submodule.span k {w} ⊔ Submodule.span k (Set.range v) = ⊤ →
        ∀ x, vanishAt φ x = ⊤ → IsWeaklyRegular (F.presheaf.stalk x :)
          (X.presheaf.germ _ x (hc x) ((φ w).f (c x)) ::
            List.ofFn fun i => X.presheaf.germ _ x (hc x) ((φ (v i)).f (c x))) := fun v hv x hx => by
      have := h (Fin.cons w v) ((hsup v).symm.trans hv) x hx
      rwa [List.ofFn_succ] at this
    obtain ⟨v, hv, hr⟩ := ih (cut F hL (φ w)) (W ⊔ Submodule.span k {w})
      (by rw [Submodule.finrank_sup_span_singleton (p := W) (hw none)]; omega) fun v hv x hx => by
        obtain ⟨q⟩ := CutDegree.nonempty_stalk_cut_equiv F hL (φ w) (c x) (hc x)
        exact (q.isWeaklyRegular_congr _).1 ((isWeaklyRegular_cons_iff _ _ _).1 (key v hv x hx)).2
    refine ⟨Fin.cons w v, (hsup v).symm.trans hv, ?_⟩
    rw [List.ofFn_succ]
    refine (regSeq_cons hL F _ _).2 ⟨(mono_cutHom_iff F hL _).2 fun x hx => ?_, hr⟩
    by_cases e : vanishAt φ x = ⊤
    · have hreg := ((isWeaklyRegular_cons_iff _ _ _).1 (key v hv x e)).1
      obtain ⟨t, ht⟩ := mem_assPoints_iff_exists.1 hx
      refine (Cartier.mem_nonzeroLocus_iff (φ w) (c x) (hc x)).2 ((X.mem_basicOpen _ x (hc x)).2 ?_)
      by_contra hu
      have h0 : t = 0 := hreg (((ht _).2 hu).trans (smul_zero _).symm)
      exact (ht 1).1 (by rw [h0, smul_zero]) isUnit_one
    · exact not_not.1 (hw (some ⟨x, hx, e⟩))

theorem nonempty_stalk_toMod {B : LB X} (hB : B.IsLB) (x : X) :
    Nonempty (((LB.toMod B).presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x) := by
  obtain ⟨e⟩ := Twist.nonempty_stalkEquiv (F := structureModule X) hB x
  let i : twist (structureModule X) B ≅ LB.toMod B := Twist.unitTwistIso B
  exact ⟨(LinearEquiv.ofBijective (stalkLinear i.hom x)
    ⟨stalkLinear_injective _ x, stalkLinear_surjective _ x⟩).symm ≪≫ₗ e ≪≫ₗ structureModuleStalkEquiv x⟩

end General

def combMap {k : Type} [Field k] (S : LinSys k) {D : ℕ} (s : Fin D → Fin S.N → k) :
    (Fin D → k) →ₛₗ[algebraMap k Γ(S.Y, ⊤)] S.L.Sec where
  toFun c := S.comb (∑ j, c j • s j)
  map_add' a b := by
    simp only [LinSys.comb, Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
  map_smul' a b := by
    simp only [LinSys.comb, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_mul]

theorem exists_regular_basis : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (s : Fin G.D → Fin G.N → K),
    G.IsGood s → ∀ B : LB G.Y, B.IsLB → ∃ g : Matrix (Fin G.D) (Fin G.D) K, IsUnit g.det ∧
      RegSeq G.isLB (GlobalTheory.LB.toMod B) (List.ofFn fun i => G.comb (∑ j, g i j • s j)) := by
  intro K _ _ G s hs B hB
  have hp := G.geom.alg.variety.proj
  have := isNoetherian_of_isProjOver hp
  have : IsFiniteQC (LB.toMod B) := isFiniteQC_iff_isFiniteType.2 ⟨LB.isQuasicoherent_toMod hB, LB.isFiniteType_toMod hB⟩
  have hfin : ((G.ideal s).support : Set G.Y).Finite := by
    have := hs.finite
    have h := ((G.ideal s).subschemeι ≫ G.str).finite_preimage_singleton (IsLocalRing.closedPoint K)
    rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
    exact (h.subset fun z _ => Subsingleton.elim (α := PrimeSpectrum K) _ _).image _
  obtain ⟨v, hv, hr⟩ := exists_regSeq (combMap G.toLinSys s) G.isLB G.chartAt G.mem_chartAt G.D (LB.toMod B) ⊥
    (by simp) fun v hv x hx => by
      rw [bot_sup_eq] at hv
      obtain ⟨q⟩ := nonempty_stalk_toMod hB x
      refine (q.isWeaklyRegular_congr _).2 ((ProperCut.topSelf_eq_length_of_smooth G.str G.smooth hp G.isLB
        (fun i => combMap G.toLinSys s (v i)) (hfin.subset fun y hy => ?_)).2.1 x ?_ _ _).toIsWeaklyRegular
      · have e := vanishAt_eq_top _ hv ((mem_support_cutIdeal _ _ y).1 hy)
        refine (mem_support_cutIdeal _ _ y).2 fun i => ?_
        have h : y ∉ nonzeroLocus (G.comb (∑ j, (Pi.single i 1 : Fin G.D → K) j • s j)) :=
          e.ge (Submodule.mem_top (x := Pi.single i 1))
        simpa [Pi.single_apply] using h
      · exact (mem_support_cutIdeal _ _ x).2 fun i => hx.ge (Submodule.mem_top (x := v i))
  rw [bot_sup_eq] at hv
  refine ⟨Matrix.of v, (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1
    (linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp))), hr⟩

end GlobalTheory.RegBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockLevelsTwistedConstantTermSplitPlace
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
  GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SplitLevels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_UL_split {n : ℕ} {w : Pl E} (hw : IsSplitAt w) (x : GLw n w) : x ∈ UL n w := by
  rw [UL, if_pos hw]; exact Subgroup.mem_top x

theorem toSub_of_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (hg : g ∈ H) : toSub H g = ⟨g, hg⟩ := by
  simp [toSub, hg]

theorem blk_zero {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) : blk h w m 0 = dgM h w m := by
  ext1
  rw [CtLevel.blk_val, dgM_val, dgMat, Matrix.mul_zero]

theorem ct_inv_blocks {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (F : GLw n w → ℂ)
    (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (hF : ∀ y ∈ N, ∀ x, F (y * x) = F x ∧ F (x * y) = F x)
    (k : GLw a w × GLw b w) (hk1 : k.1 ∈ GlobalTheory.LFun.KGL w a) (hk2 : k.2 ∈ GlobalTheory.LFun.KGL w b) (hkN : dgM h w k ∈ N)
    (m : GLw a w × GLw b w) : ct h w F (k * m) = ct h w F m ∧ ct h w F (m * k) = ct h w F m := by
  have hab := GlobalTheory.T.absHalf_blockDet_integralGL_invariant E a b w m k hk1 hk2
  constructor
  · unfold ct
    rw [hab.1]
    congr 2
    funext X
    congr 1
    funext κ
    rw [(GlobalTheory.T.blockUpperTimesUnipotent_mul_blockDiagonal E a b n h w m k _).1]
    have e : (κ : GLw n w)⁻¹ * (dgM h w k * blk h w m (Multiplicative.toAdd X)) * κ =
        ((κ : GLw n w)⁻¹ * dgM h w k * κ) * ((κ : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * κ) := by group
    rw [e, (hF _ (hNn _ κ.2 _ hkN) _).1]
  · unfold ct
    have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        avg fun κ : GlobalTheory.LFun.KGL w n => F ((κ : GLw n w)⁻¹ * blk h w (m * k) (Multiplicative.toAdd X) * κ)) =
        fun X => avg fun κ : GlobalTheory.LFun.KGL w n => F ((κ : GLw n w)⁻¹ *
          blk h w m (Multiplicative.toAdd (Multiplicative.ofAdd (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val))) * κ) := by
      funext X
      congr 1
      funext κ
      rw [(GlobalTheory.T.blockUpperTimesUnipotent_mul_blockDiagonal E a b n h w m k _).2]
      have e : (κ : GLw n w)⁻¹ * (blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * dgM h w k) * κ =
          ((κ : GLw n w)⁻¹ * blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * κ) *
            ((κ : GLw n w)⁻¹ * dgM h w k * κ) := by group
      rw [e, (hF _ (hNn _ κ.2 _ hkN) _).2]
      rfl
    have hh := GlobalTheory.T.haarIntegralNormalized_integralMatrices_twoSidedMul E a b w (fun Y => avg fun κ : GlobalTheory.LFun.KGL w n =>
      F ((κ : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd Y) * κ)) k.1 k.2⁻¹ hk1 (inv_mem hk2)
    rw [hab.2, e, hh]

theorem ctMu_inv_blocks {a b n : ℕ} (h : a + b = n) (w : Pl E) (hw : IsSplitAt w) (N : Subgroup (GLw n w))
    (K' : Subgroup (UL n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ) (hf : IsHecke K' f)
    (hNK : N ≤ K'.map (UL n w).subtype) (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (k : GLw a w × GLw b w) (hk : k ∈ (lev₁ h w N μ).prod (lev₂ h w N μ)) (m : GLw a w × GLw b w) :
    ctMu h w μ f (k * m) = ctMu h w μ f m ∧ ctMu h w μ f (m * k) = ctMu h w μ f m := by
  obtain ⟨⟨⟨hk1, hkN1⟩, hkμ1⟩, ⟨⟨hk2, hkN2⟩, hkμ2⟩⟩ := hk
  have hkN : dgM h w k ∈ N := by
    have e : k = (k.1, 1) * (1, k.2) := by ext <;> simp
    rw [e, map_mul]
    exact N.mul_mem hkN1 hkN2
  have hF : ∀ y ∈ N, ∀ x, (fun y => f (toSub (UL n w) y)) (y * x) = (fun y => f (toSub (UL n w) y)) x ∧
      (fun y => f (toSub (UL n w) y)) (x * y) = (fun y => f (toSub (UL n w) y)) x := by
    intro y hy x
    obtain ⟨y', hy', rfl⟩ := hNK hy
    have e1 : toSub (UL n w) ((UL n w).subtype y' * x) = y' * toSub (UL n w) x := by
      rw [toSub_of_mem _ _ (mem_UL_split hw _), toSub_of_mem _ _ (mem_UL_split hw x)]; rfl
    have e2 : toSub (UL n w) (x * (UL n w).subtype y') = toSub (UL n w) x * y' := by
      rw [toSub_of_mem _ _ (mem_UL_split hw _), toSub_of_mem _ _ (mem_UL_split hw x)]; rfl
    exact ⟨by simp only; rw [e1]; exact (hf.2 y' hy' _).1, by simp only; rw [e2]; exact (hf.2 y' hy' _).2⟩
  have hc := ct_inv_blocks h w N (fun y => f (toSub (UL n w) y)) hNn hF k hk1 hk2 hkN m
  have hμ1 : μ (GeneralLinearGroup.det k.1) = 1 := hkμ1
  have hμ2 : μ (GeneralLinearGroup.det k.2) = 1 := hkμ2
  unfold ctMu
  rw [hc.1, hc.2]
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow, map_pow, hμ1, hμ2, one_pow, mul_one, one_mul]
  constructor <;> trivial

theorem levels_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E),
    IsSplitAt w → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen {x | μ x = 1} → ∀ K' : Subgroup (UL n w),
    IsLevel (MonoidHom.id _) (KL n w) K' → ∃ (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw (n - a) w))
      (K'' : Subgroup (GLw n w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) K₁ ∧
      IsLevel (thL (n - a) w) (GlobalTheory.LFun.KGL w (n - a)) K₂ ∧
      ((K' = KL n w ∧ ∀ u ∈ (GlobalTheory.LFun.KGL w 1), μ (GeneralLinearGroup.det u) = 1) →
        K₁ = GlobalTheory.LFun.KGL w a ∧ K₂ = GlobalTheory.LFun.KGL w (n - a)) ∧
      IsOpen (K'' : Set (GLw n w)) ∧ K'' ≤ K'.map (UL n w).subtype ∧
      (K''.subgroupOf (GlobalTheory.LFun.KGL w n)).Normal ∧
      (∀ m₁ ∈ K₁, ∀ m₂ ∈ K₂, blk (Nat.add_sub_cancel' ha) w (m₁, m₂) 0 ∈ K'') ∧
      (∀ m₁ ∈ K₁, ∀ m₂ ∈ K₂, μ (GeneralLinearGroup.det m₁ ^ (n - a) * GeneralLinearGroup.det m₂ ^ a) = 1) ∧
      ∀ f, IsHecke K' f → IsHecke (K₁.prod K₂) (ctMu (Nat.add_sub_cancel' ha) w μ f) := by
  intro E _ _ _ n a ha w hw μ hμ K' hK'
  obtain ⟨N, hNo, hNK, hNn, hNf⟩ := GlobalTheory.T.exists_open_conjStable_subgroup_of_splitLevel E n w K' hw hK'
  have hlev := GlobalTheory.T.isLevel_blockLevels_splitPlace E a (n - a) n (Nat.add_sub_cancel' ha) w N μ hw hNo hμ
  refine ⟨lev₁ (Nat.add_sub_cancel' ha) w N μ, lev₂ (Nat.add_sub_cancel' ha) w N μ, N, hlev.1, hlev.2, ?_, hNo, hNK,
    ?_, ?_, ?_, fun f hf => ⟨GlobalTheory.T.hasCompactSupport_twistedConstantTermSplitPlace E a (n - a) n _ w μ f hw hf.1, fun k hk m =>
      ctMu_inv_blocks _ w hw N K' μ f hf hNK hNn k hk m⟩⟩
  · rintro ⟨hK'e, hμ1⟩
    rw [hNf hK'e]
    exact GlobalTheory.T.blockLevels_eq_integralGL_of_unramified E a (n - a) n _ w μ hμ1
  · refine ⟨fun x hx k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := hNn _ (inv_mem k.2) _ hx
    simpa [mul_assoc] using this
  · intro m₁ hm₁ m₂ hm₂
    rw [blk_zero]
    have e : ((m₁, m₂) : GLw a w × GLw (n - a) w) = (m₁, 1) * (1, m₂) := by ext <;> simp
    rw [e, map_mul]
    exact N.mul_mem hm₁.1.2 hm₂.1.2
  · intro m₁ hm₁ m₂ hm₂
    have h1 : μ (GeneralLinearGroup.det m₁) = 1 := hm₁.2
    have h2 : μ (GeneralLinearGroup.det m₂) = 1 := hm₂.2
    rw [map_mul, map_pow, map_pow, h1, h2, one_pow, one_pow, mul_one]

end GlobalTheory.BCT.SplitLevels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCellUAbsorbUnip
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

noncomputable section

namespace GlobalTheory.WeylCell.WeylUnipotentShell

section BlockKeep

variable {R : Type} [CommRing R] {n : ℕ}

def blockKeep (a b : Fin n) (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if (a ≤ i ∧ i ≤ b) ∧ (a ≤ j ∧ j ≤ b) then A i j else (1 : Matrix (Fin n) (Fin n) R) i j

theorem blockKeep_one (a b : Fin n) : blockKeep a b (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j; unfold blockKeep; split_ifs <;> rfl

theorem blockKeep_mul (a b : Fin n) (A B : Matrix (Fin n) (Fin n) R) (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) : blockKeep a b (A * B) = blockKeep a b A * blockKeep a b B := by
  ext i j
  by_cases hi : a ≤ i ∧ i ≤ b
  · by_cases hj : a ≤ j ∧ j ≤ b
    · simp only [blockKeep, Matrix.mul_apply, if_pos (And.intro hi hj)]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : a ≤ k ∧ k ≤ b
      · rw [if_pos ⟨hi, hk⟩, if_pos ⟨hk, hj⟩]
      · rw [if_neg (fun h => hk h.2), Matrix.one_apply_ne (by rintro rfl; exact hk hi), zero_mul]
        rcases not_and_or.1 hk with h | h
        · rw [hA i k (lt_of_lt_of_le (not_le.1 h) hi.1), zero_mul]
        · rw [hB k j (lt_of_le_of_lt hj.2 (not_le.1 h)), mul_zero]
    · have hcol : ∀ k, blockKeep a b B k j = (1 : Matrix (Fin n) (Fin n) R) k j := fun k => if_neg (fun h => hj h.2)
      rw [Matrix.mul_apply]
      simp only [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [blockKeep, hi, hj, and_false, if_false, true_and, Matrix.one_apply]
  · have hrow : ∀ k, blockKeep a b A i k = (1 : Matrix (Fin n) (Fin n) R) i k := fun k => if_neg (fun h => hi h.1)
    rw [Matrix.mul_apply]
    simp only [hrow, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [blockKeep, hi, false_and, if_false, Matrix.one_apply]

end BlockKeep

section Keep

variable {L : Type} [Field L] {n : ℕ}

def blockKeepGL (a b : Fin n) (g : GL (Fin n) L) (hg : g ∈ unipB L (Fin n)) : GL (Fin n) L where
  val := blockKeep a b (g : Matrix (Fin n) (Fin n) L)
  inv := blockKeep a b ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  val_inv := by
    rw [← blockKeep_mul a b _ _ ((mem_unipB L).1 hg).1 ((mem_unipB L).1 (inv_mem hg)).1, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, blockKeep_one]
  inv_val := by
    rw [← blockKeep_mul a b _ _ ((mem_unipB L).1 (inv_mem hg)).1 ((mem_unipB L).1 hg).1, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, blockKeep_one]

theorem blockKeepGL_mem_GU [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} (a : Fin n) (g : GL (Fin n) L)
    (hg : g ∈ unipB L (Fin n)) (hG : g ∈ GU σ n) : blockKeepGL a a.rev g hg ∈ GU σ n := by
  rw [LGrp.mem_GU_iff] at hG ⊢
  intro i j
  show blockKeep a a.rev ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
    σ (blockKeep a a.rev (g : Matrix (Fin n) (Fin n) L) j.rev i.rev)
  have key : ∀ i : Fin n, (a ≤ i.rev ∧ i.rev ≤ a.rev) ↔ (a ≤ i ∧ i ≤ a.rev) := by
    intro i
    have := i.isLt
    have := a.isLt
    simp only [Fin.le_iff_val_le_val, Fin.val_rev]
    omega
  unfold blockKeep
  simp only [key]
  by_cases h : (a ≤ i ∧ i ≤ a.rev) ∧ (a ≤ j ∧ j ≤ a.rev)
  · rw [if_pos h, if_pos h.symm, hG]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), Matrix.one_apply, Matrix.one_apply, apply_ite σ, map_one, map_zero]
    simp only [Fin.rev_inj, eq_comm (a := j)]

theorem blockKeep_eq_self (a b : Fin n) (A : Matrix (Fin n) (Fin n) L) (h1 : ∀ i j, j < i → A i j = 0)
    (h2 : ∀ i, A i i = 1) (h3 : ∀ i j, i < j → (i < a ∨ b < j) → A i j = 0) : blockKeep a b A = A := by
  ext i j
  unfold blockKeep
  split_ifs with h
  · rfl
  · rcases lt_trichotomy i j with hij | rfl | hij
    · rw [Matrix.one_apply_ne hij.ne, h3 i j hij]
      by_contra hc
      rw [not_or, not_lt, not_lt] at hc
      exact h ⟨⟨hc.1, hij.le.trans hc.2⟩, hc.1.trans hij.le, hc.2⟩
    · rw [Matrix.one_apply_eq, h2]
    · rw [Matrix.one_apply_ne hij.ne', h1 i j hij]

end Keep

end GlobalTheory.WeylCell.WeylUnipotentShell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFiniteExtensionGaloisRepsCharactersStatement
section
open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_finiteExtension_galoisReps_characters : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n a t : ℕ) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (ρ : G E Ω →* GL (Fin a) (PadicAlgCl l)) (χ : Fin t → G E Ω →* (PadicAlgCl l)ˣ), Continuous r → Continuous ρ → (∀ s, Continuous (GlobalTheory.TripleGal.rk1 (χ s))) → ∃ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) ∧ (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) ∧ (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ g i j, (ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ s g, ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ LL.1 := by
  first | exact @GlobalTheory.RepFinExtJoint.finext_joint | exact GlobalTheory.RepFinExtJoint.finext_joint | (intros; apply GlobalTheory.RepFinExtJoint.finext_joint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactBoxOfUnitaryTranslateCompactStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactBox_of_unitaryTranslate_compact : ∀ (D : D7) (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.InBox K (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) → GlobalTheory.Unf.InBox K' x := by
  first | exact @GlobalTheory.BoxMove.inBox_image_mul | exact GlobalTheory.BoxMove.inBox_image_mul | (intros; apply GlobalTheory.BoxMove.inBox_image_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupSchemeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cotangent_frame_smooth_groupScheme : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] [Smooth A.hom] (x : Sp O), ∃ (U : (Sp O).Opens) (n : ℕ) (s : Fin n → Γ(GlobalTheory.LieVB.omega A, U)), x ∈ U ∧ GlobalTheory.VB.IsFrame s := by
  first | exact @GlobalTheory.ConormalFrame.exists_isFrame_omega | exact GlobalTheory.ConormalFrame.exists_isFrame_omega | (intros; apply GlobalTheory.ConormalFrame.exists_isFrame_omega <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorBoundMatrixMulStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_bound_matrix_mul : ∀ (E κ ι : Type) [Field E] [NumberField E] [Fintype κ] [Fintype ι] (T : Matrix κ ι E), ∃ M : ℕ, 0 < M ∧ ∀ (L : ℕ) (x : ι → E), (∀ i, IsIntegral ℤ ((L : E) * x i)) → ∀ k, IsIntegral ℤ (((M * L : ℕ) : E) * ∑ i, T k i * x i) := by
  first | exact @GlobalTheory.denom_bound_mul | exact GlobalTheory.denom_bound_mul | (intros; apply GlobalTheory.denom_bound_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteIndexLeviSubgroupUnipotentConjIntegrStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteIndex_levi_subgroup_unipotentConj_integral : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), ∃ U : Subgroup (GLw a w × GLw b w), U ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) ∧ U.relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ≠ 0 ∧ ∀ k ∈ U, (blk h w 1 X)⁻¹ * blk h w k 0 * blk h w 1 X ∈ GlobalTheory.LFun.KGL w n := by
  first | exact @GlobalTheory.LeviDesc.ConjStab.exists_stab | exact GlobalTheory.LeviDesc.ConjStab.exists_stab | (intros; apply GlobalTheory.LeviDesc.ConjStab.exists_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPairFlagsDifferingOneStepStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_pair_flags_differing_one_step : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∃ ψ₂ : Y.Fn →+* RatFunc Y.Fn, GenPair Y (algebraMap Y.Fn (RatFunc Y.Fn)) ψ₂ ∧ (∀ u : X.Fn, algebraMap Y.Fn (RatFunc Y.Fn) (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (shear τ a b (RatFunc.X : RatFunc Y.Fn) * (B.map (algebraMap Y.Fn (RatFunc Y.Fn)) * (B.map ψ₂)⁻¹)) := by
  first | exact @GlobalTheory.FlagPush.Gen.exists_genPair | exact GlobalTheory.FlagPush.Gen.exists_genPair | (intros; apply GlobalTheory.FlagPush.Gen.exists_genPair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGenerationAmplePairMultiplesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalGeneration_ample_pair_multiples : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ j : ℕ, GenAt P (c₀ * j) := by
  first | exact @GlobalTheory.HSNef.AmpleGen.exists_genAt_mul | exact GlobalTheory.HSNef.AmpleGen.exists_genAt_mul | (intros; apply GlobalTheory.HSNef.AmpleGen.exists_genAt_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonFormStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_positive_petersson_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ B : GlobalTheory.DefU.autU E n →ₗ⋆[ℂ] GlobalTheory.DefU.autU E n →ₗ[ℂ] ℂ, (∀ u v, star (B u v) = B v u) ∧ (∀ v, 0 ≤ (B v v).re) ∧ (∀ v, B v v = 0 → v = 0) ∧ ∀ g u v, B (GlobalTheory.DefU.autRep E n g u) (GlobalTheory.DefU.autRep E n g v) = B u v := by
  first | exact @GlobalTheory.DefU.Petersson.exists_invariant_pos_form | exact GlobalTheory.DefU.Petersson.exists_invariant_pos_form | (intros; apply GlobalTheory.DefU.Petersson.exists_invariant_pos_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsOpenSubgroupAdicUnitsNoRootsOfUnityStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isOpen_subgroup_adicUnits_no_rootsOfUnity : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ V : Subgroup (w.adicCompletion E)ˣ,
    IsOpen (V : Set (w.adicCompletion E)ˣ) ∧ ∀ t : Eˣ, (∃ n : ℕ, 0 < n ∧ t ^ n = 1) →
      Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom t ∈ V → t = 1 := by
  first | exact @GlobalTheory.RootOpen.exists_open_subgroup_no_roots | exact GlobalTheory.RootOpen.exists_open_subgroup_no_roots | (intros; apply GlobalTheory.RootOpen.exists_open_subgroup_no_roots <;> assumption)
end

