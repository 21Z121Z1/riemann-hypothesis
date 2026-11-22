import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0064
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCdvrCompletionIntegralIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSupportBoundedByUniformizerPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FunObj.FlatSupp

open GlobalTheory.RootEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_inv_pow {ϖ : kˣ} (n : ℕ) :
    valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) = (valuation k (ϖ : k) ^ n)⁻¹ := by
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]

theorem val_inv_pow_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {n n' : ℕ} (h : n ≤ n') :
    valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) ≤ valuation k (((ϖ ^ n')⁻¹ : kˣ) : k) := by
  rw [val_inv_pow, val_inv_pow]
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  exact inv_anti₀ (pow_pos (zero_lt_iff.2 h0) _) (pow_le_pow_of_le_one zero_le' h1 h)

theorem exists_le {ϖ : kˣ} (hϖ : IsUnif ϖ) (a : k) :
    ∃ n : ℕ, valuation k a ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  have hv : valuation k a ≠ 0 := by simpa using ha
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (hϖ ▸ uniformizer_lt_one : valuation k (ϖ : k) < 1) (Units.mk0 _ hv)⁻¹
  refine ⟨n, ?_⟩
  rw [val_inv_pow]
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0] at hn
  have := le_of_lt hn
  rwa [le_inv_comm₀ (pow_pos (zero_lt_iff.2 h0) _) (zero_lt_iff.2 hv)] at this

theorem exists_bound_conj {ϖ : kˣ} (hϖ : IsUnif ϖ) {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : GL m k) (B : GL n k) :
    ∃ N : ℕ, ∀ Z : Matrix m n k, (∀ r s, ((A⁻¹ : GL m k).val * Z * B.val) r s ∈ 𝒪[k]) →
      ∀ r s, valuation k (Z r s) ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) := by
  classical
  choose nA hnA using fun p : m × m => exists_le hϖ (A.val p.1 p.2)
  choose nB hnB using fun p : n × n => exists_le hϖ ((B⁻¹ : GL n k).val p.1 p.2)
  set N0 := Finset.univ.sup nA ⊔ Finset.univ.sup nB
  have hc : valuation k (((ϖ ^ (N0 + N0))⁻¹ : kˣ) : k) =
      valuation k (((ϖ ^ N0)⁻¹ : kˣ) : k) * valuation k (((ϖ ^ N0)⁻¹ : kˣ) : k) := by
    rw [val_inv_pow, val_inv_pow, pow_add, mul_inv]
  set c := valuation k (((ϖ ^ N0)⁻¹ : kˣ) : k)
  have hA : ∀ r a, valuation k (A.val r a) ≤ c := fun r a =>
    (hnA (r, a)).trans (val_inv_pow_mono hϖ (le_sup_left.trans' (Finset.le_sup (f := nA) (Finset.mem_univ (r, a)))))
  have hB : ∀ b s, valuation k ((B⁻¹ : GL n k).val b s) ≤ c := fun b s =>
    (hnB (b, s)).trans (val_inv_pow_mono hϖ (le_sup_right.trans' (Finset.le_sup (f := nB) (Finset.mem_univ (b, s)))))
  refine ⟨N0 + N0, fun Z hZ r s => ?_⟩
  have hZ' : Z = A.val * ((A⁻¹ : GL m k).val * Z * B.val) * (B⁻¹ : GL n k).val := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, Units.mul_inv,
      Matrix.one_mul]
  rw [hZ', hc]
  set W := (A⁻¹ : GL m k).val * Z * B.val
  simp only [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun b _ => ?_
  rw [map_mul]
  refine mul_le_mul' (Valuation.map_sum_le _ fun a _ => ?_) (hB b s)
  rw [map_mul]
  simpa using mul_le_mul' (hA r a) (show valuation k (W a b) ≤ 1 from hZ a b)

open Matrix in

theorem flatTensor_support : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → (∀ j, j < G.m → ∀ r s, (j + 1 = G.m → r ≠ topLast G (j + 1)) → valuation k (x j r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ i, i < G.m → ∀ r s, valuation k (y i r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  classical
  intro k _ _ _ _ _ _ G hs ψ ν ϖ e T keep g hϖ hT
  choose N hN using fun b : Edge => exists_bound_conj hϖ (Assignment.one.read (g b.tgt)) (Assignment.one.read (g b.src))
  refine ⟨(oppositePath G.m).toFinset.sup N, fun x y hne => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, flatIntegrand hs ψ (moved G keep g T) x y v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    unfold flatTensor
    simp [h]
  have hT0 : T (G.moveArgs .one g (fill hs x y v)) ≠ 0 := by
    intro h0
    apply hv
    simp [flatIntegrand, moved, Grid.pathAct, h0]
  have key : ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (fill hs x y v b r s) ≤
      valuation k (((ϖ ^ (oppositePath G.m).toFinset.sup N)⁻¹ : kˣ) : k) := by
    intro b hb r s
    refine le_trans (hN b _ (fun r s => ?_) r s)
      (val_inv_pow_mono hϖ (Finset.le_sup (f := N) (List.mem_toFinset.2 hb)))
    have hm : (G.moveArgs .one g (fill hs x y v)) b ∈ matLat _ (GlobalTheory.SplitFlip.stdLat k _) := by
      by_contra h
      exact hT0 (hT.2.1 _ b hb h)
    exact mem_matLat_stdLat.1 hm r s
  refine ⟨fun j hj r s hr => ?_, fun i hi r s => ?_⟩
  · have hmem : Edge.theta G.m j ∈ oppositePath G.m := by simp [oppositePath]; omega
    by_cases hj' : j < G.m - 1
    · have h := key _ hmem (frame (b := G.rank (G.m, j)) (c := G.m - 2 - j + 1) (by have := topRank_add hs j; omega) (Sum.inl s))
        (frame (b := G.rank (G.m, j + 1)) (c := G.m - 2 - j) (by have := topRank_add hs (j + 1); omega) (Sum.inl r))
      rw [fill_theta, transpose_apply, downMap, dif_pos hj'] at h
      simpa [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, stepPt, basePt, Free, Kept] using h
    · have hjm : j + 1 = G.m := by omega
      have hrk := topRank_add hs (j + 1)
      have hrk' := topRank_add hs j
      have hr' : r.val < G.rank (G.m, j + 1) := by
        have := hr hjm
        have h2 : (topLast G (j + 1)).val = topRank G (j + 1) - 1 := rfl
        rw [Ne, Fin.ext_iff, h2] at this
        have := r.2
        omega
      have h := key _ hmem (show Fin (G.rank (G.m, j)) from ⟨s.val, by have := s.2; omega⟩)
        (show Fin (G.rank (G.m, j + 1)) from ⟨r.val, hr'⟩)
      rw [fill_theta, transpose_apply, downMap, dif_neg hj', dif_pos hjm] at h
      simpa using h
  · have hmem : Edge.ex i G.m ∈ oppositePath G.m := by simp [oppositePath]; omega
    have h := key _ hmem s r
    rwa [fill_ex, transpose_apply] at h

end GlobalTheory.FunObj.FlatSupp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointCoordinatesMemSpanEigenLattice
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace GlobalTheory.PtDeg.FrameEig

theorem dualMapR_epsScaleR {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (a : R) :
    spMap (Chart.dualMapR f) ≫ spMap (epsScaleR a) = spMap (epsMul (f a)) ≫ spMap (Chart.dualMapR f) := by
  rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
  congr 1
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, epsScaleR, Chart.dualMapR, mul_comm]

theorem epsScaleR_epsMul_comm {R : Type} [CommRing R] (a b : R) :
    spMap (epsScaleR a) ≫ spMap (epsMul b) = spMap (epsMul b) ≫ spMap (epsScaleR a) := by
  rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
  congr 1
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, epsScaleR, mul_left_comm]

theorem scale_eig {R : Type} [CommRing R] {X : Scheme.{0}} (a b : R) (x : Sp (DualNumber R) ⟶ X) (g : X ⟶ X)
    (h : x ≫ g = spMap (epsMul b) ≫ x) :
    (spMap (epsScaleR a) ≫ x) ≫ g = spMap (epsMul b) ≫ spMap (epsScaleR a) ≫ x := by
  rw [Category.assoc, h, ← Category.assoc, epsScaleR_epsMul_comm, Category.assoc]

theorem epsScaleR_eq_epsMul {R : Type} [CommRing R] (a : R) : epsScaleR a = epsMul a := rfl

theorem sc_left {R : Type} [CommRing R] {G : Over (Sp R)} (a : R) (v : epsR R ⟶ G) :
    (GlobalTheory.CM.IntCoord.sc a ≫ v).left = spMap (epsScaleR a) ≫ v.left := rfl

end GlobalTheory.PtDeg.FrameEig

open GlobalTheory.PtDeg.FrameEig in

theorem GlobalTheory.PtDeg.frameCoord_mem_span_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ j, u j ∈ Submodule.span K (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu j
  obtain ⟨u₀, w, h₁, h₂, hc⟩ := hu j
  have h₂' : u₀ ≫ m2.cm.F = w.left ≫ F.φ := h₂
  have h₁' : u₀ ≫ m1.cm.F = y.u ρ j := h₁

  have hbase : u₀ ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
    apply GlobalTheory.IntLie.spMap_frac_cancel (V := 𝓞 K)
    rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, h₂', Category.assoc]
    have e := F.fib.2.1.1.w
    erw [e]
    rw [← Category.assoc, Over.w w]
    rfl

  have hact0 : ∀ a : 𝓞 E, u₀ ≫ (t₀.act.act a).left = spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ u₀ := by
    intro a
    apply m1.cart.1.hom_ext
    · rw [Category.assoc, m1.act a, ← Category.assoc, h₁', y.eig ρ j a, htt a, Category.assoc, h₁']
    · rw [Category.assoc, Over.w (t₀.act.act a), hbase, Category.assoc, hbase, GlobalTheory.IntLie.spMap_comp₂,
        GlobalTheory.IntLie.epsMul_alg]

  have hw : ∀ a : 𝓞 E, w.left ≫ F.φ ≫ (B.t.act.act a).left =
      spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ w.left ≫ F.φ := by
    intro a
    rw [← reassoc_of% h₂', ← m2.act a, ← Category.assoc, hact0, Category.assoc, h₂']

  have hc' : u j ∈ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) := by
    rw [(GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K B.pol F).2]; trivial
  obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ (u j) hc'
  rw [Submodule.span_eq, Submonoid.smul_def] at hd
  obtain ⟨-, -, -, -, hlat, heig⟩ := GlobalTheory.CM.integral_tangent_coordinates K B.pol F
  obtain ⟨U, hUt, w₁, hUv, hw₁⟩ := (hlat _).1 hd
  have := F.P₀.isAb.comm
  have hK := GlobalTheory.LieComb.lieComb_algebra K F.P₀.A _ F.v F.basis.1
  set dK : K := algebraMap (𝓞 K) K (d : 𝓞 K) with hdK
  have hw₁' : w₁ = GlobalTheory.CM.IntCoord.sc dK ≫ w := by
    have h3 := hK.2.2.1 1 ![u j] ![w] ![dK] _ (fun i => by fin_cases i; exact hc)
      ((GlobalTheory.CM.IntCoord.isLieComb_one_iff _ _ _).2 rfl)
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one,
      Finset.sum_singleton] at h3
    rw [← algebraMap_smul K (d : 𝓞 K) (u j)] at hw₁
    exact (hK.1 _).unique hw₁ h3
  have hw₁e : ∀ a : 𝓞 E, w₁.left ≫ F.φ ≫ (B.t.act.act a).left =
      spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ w₁.left ≫ F.φ := by
    intro a
    rw [hw₁', sc_left, Category.assoc, Category.assoc]
    have := scale_eig dK ((tt a : 𝓞 K) : K) (w.left ≫ F.φ) (B.t.act.act a).left (by rw [Category.assoc, hw a])
    simpa only [Category.assoc] using this

  have := B.pol.isAb.proper
  have hmem : (d : 𝓞 K) • u j ∈ F.eigLat B.t.act tt := by
    rw [heig]
    refine ⟨U, ⟨hUt, w₁, hUv, hw₁⟩, fun a => ?_⟩
    rw [GlobalTheory.CM.IntCoord.isLieComb_one_iff]
    have hv1 : IsVecOver (algebraMap (𝓞 K) K) F.φ (U ≫ B.t.act.act a)
        (GlobalTheory.CM.IntCoord.sc ((tt a : 𝓞 K) : K) ≫ w₁) := by
      unfold IsVecOver at hUv ⊢
      rw [sc_left, Over.comp_left, ← Category.assoc, ← hUv, Category.assoc, Category.assoc, hw₁e a,
        epsScaleR_eq_epsMul]
    have hv2 : IsVecOver (algebraMap (𝓞 K) K) F.φ (GlobalTheory.CM.IntCoord.sc (tt a) ≫ U)
        (GlobalTheory.CM.IntCoord.sc ((tt a : 𝓞 K) : K) ≫ w₁) := by
      unfold IsVecOver at hUv ⊢
      rw [sc_left, sc_left, Category.assoc, hUv, epsScaleR_eq_epsMul]
      have e := dualMapR_epsScaleR (algebraMap (𝓞 K) K) (tt a)
      exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.left) e).trans (Category.assoc _ _ _))).symm
    exact GlobalTheory.CM.IntCoord.eq_of_isVecOver (IsFractionRing.injective (𝓞 K) K) hv1 hv2

  have hd0 : dK ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.coe_ne_zero d)
  have h₃ := Submodule.smul_mem (Submodule.span K (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K))) dK⁻¹
    (Submodule.subset_span hmem)
  rwa [← algebraMap_smul K (d : 𝓞 K) (u j), ← hdK, inv_smul_smul₀ hd0] at h₃
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointGenericFibreCoordinatesEqFrame
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

namespace GlobalTheory.PtDeg.FrameGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem over_of_fib {K : Type} [Field K] [NumberField K] {B : GlobalTheory.CM.PAT H (Sp (𝓞 K))} {t₀ : SAB H (Sp K)}
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol)
    (u₀ : Sp (DualNumber K) ⟶ t₀.G.left) (w : epsR K ⟶ F.P₀.A) (h : u₀ ≫ m2.φ = w.left ≫ F.φ) :
    u₀ ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
  haveI : Epi (CommRingCat.ofHom (algebraMap (𝓞 K) K)) := IsLocalization.epi (nonZeroDivisors (𝓞 K)) K
  haveI : Mono (spMap (algebraMap (𝓞 K) K)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  rw [← cancel_mono (spMap (algebraMap (𝓞 K) K)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, h,
    Category.assoc]
  have := F.fib.2.1.1.w
  erw [this, ← Category.assoc, Over.w w]
  rfl

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg.FrameGen

theorem spMap_dualMap_algebraMap {S R : Type} [CommRing S] [CommRing R] (f : S →+* R) :
    spMap (dualMap f) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap R (DualNumber R)) ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_dualMap_id {S : Type} [CommRing S] : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
  have : dualMap (RingHom.id S) = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply TrivSqZeroExt.ext <;> simp [dualMap]
  simp only [spMap, this]
  exact Spec.map_id _

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg.FrameGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_lift_eps {K Tf : Type} [CommRing K] [CommRing Tf] {G' : Over (Sp Tf)} {G : Over (Sp K)}
    (f : K →+* Tf) {φ : G'.left ⟶ G.left} (hp : IsPullback φ G'.hom G.hom (spMap f))
    (u₀ : Sp (DualNumber K) ⟶ G.left) (hu : u₀ ≫ G.hom = spMap (algebraMap K (DualNumber K))) :
    ∃ g : epsR Tf ⟶ G', g.left ≫ φ = spMap (dualMap f) ≫ u₀ :=
  ⟨Over.homMk (hp.lift (spMap (dualMap f) ≫ u₀) (spMap (algebraMap Tf (DualNumber Tf)))
      (by rw [Category.assoc, hu, spMap_dualMap_algebraMap])) (hp.lift_snd _ _ _), hp.lift_fst _ _ _⟩

theorem isLieComb_of_match {K : Type} [Field K] [NumberField K] {B : GlobalTheory.CM.PAT H (Sp (𝓞 K))} {t₀ : SAB H (Sp K)}
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) {T : CDVR} (iK : K →+* T.Fr)
    {t' : SAB H (Sp T.Fr)} (n' : SABMap t' t₀ (spMap iK)) {v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)}
    (hv' : IsLieBasis v')
    (hv'φ : ∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (dualMap iK) ≫ (F.v k).left ≫ F.φ)
    (c : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A) (hw : IsLieComb c F.v w) (g : epsR T.Fr ⟶ t'.G)
    (hg : g.left ≫ n'.φ ≫ m2.φ = spMap (dualMap iK) ≫ w.left ≫ F.φ) :
    IsLieComb (fun k => iK (c k)) v' g := by
  obtain ⟨w', hw'⟩ := ((GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1).1 (fun k => iK (c k))).exists
  have hpb := IsGrpPullback.comp n'.cart m2.cart
  have hid : spMap (RingHom.id T.Fr) = 𝟙 _ := by
    simp only [spMap, CommRingCat.ofHom_id]
    exact Spec.map_id _
  have key := GlobalTheory.LamT.LetterInt.comb_match hpb F.fib.2.1 (RingHom.id T.Fr) iK
    (by rw [hid, Category.id_comp]) (v₁ := v') (v₂ := F.v)
    (fun k => by rw [spMap_dualMap_id, Category.id_comp]; exact hv'φ k) (c₁ := fun k => iK (c k)) (c₂ := c)
    (fun k => rfl) hw' hw
  rw [spMap_dualMap_id, Category.id_comp, ← hg] at key
  have : w' = g := Over.OverMorphism.ext (hpb.1.hom_ext key (by rw [Over.w w', Over.w g]))
  subst this
  exact hw'

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg.FrameGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem comb_left_of_isCombAt {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {Tf : Type} [CommRing Tf]
    {x : Sp Tf ⟶ Xo.X} {t' : SAB H (Sp Tf)} (m1' : SABMap t' Xo.univ.t x) {m : ℕ}
    (e : Fin m → (Sp (DualNumber Tf) ⟶ Xo.univ.t.G.left)) (cc : Fin m → Tf)
    (z : Sp (DualNumber Tf) ⟶ Xo.univ.t.G.left) (hz : IsCombAt x e cc z) (g : Fin m → (epsR Tf ⟶ t'.G))
    (hg : ∀ j, (g j).left ≫ m1'.φ = e j) (w'' : epsR Tf ⟶ t'.G) (hw : IsLieComb cc g w'') :
    w''.left ≫ m1'.φ = z := by
  obtain ⟨b, hb, rfl⟩ := hz
  obtain ⟨a, ha, rfl⟩ := hw
  have := GlobalTheory.LamT.LetterInt.prod_pull m1'.cart (epsR Tf) _ (𝟙 _) (by rw [Category.id_comp]; rfl) a b
    (fun j => by rw [hb j, Category.id_comp, ha j, Category.assoc, hg j]; rfl)
  rw [this, Category.id_comp]

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg

open GlobalTheory.PtDeg.FrameGen in
theorem frame_genFib_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (T : CDVR) (iK : K →+* T.Fr), letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x), m1'.φ = n'.φ ≫ m1.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → ∀ (i : Fin (Dw.mult ρ)) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), u'' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) → u'' ≫ m1'.φ = y'.u ρ i → ∃ w'' : epsR T.Fr ⟶ t'.G, w''.left = u'' ∧ IsLieComb (∑ j, C ρ i j • fun k => iK (u j k)) v' w'' := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ u hF T iK
  letI : Algebra c.F T.Fr := (iK.comp (algebraMap c.F K)).toAlgebra
  intro yT hyT t' n' m1' h1 v' hv' hv'φ C a y' hchg i u'' hu''0 hu''1
  choose u₀ w hu₁ hu₂ hw using hF
  have hover : ∀ j, u₀ j ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) :=
    fun j => over_of_fib m2 F (u₀ j) (w j) (hu₂ j)
  choose g hg using fun j => exists_lift_eps iK n'.cart.1 (u₀ j) (hover j)
  have hg1 : ∀ j, (g j).left ≫ m1'.φ = yT.u ρ j := fun j => by
    rw [h1, ← Category.assoc, hg j, Category.assoc, hu₁ j]
    exact (hyT.2.1 ρ j).symm
  have hcomb : ∀ j, IsLieComb (fun k => iK (u j k)) v' (g j) := fun j =>
    isLieComb_of_match m2 F iK n' hv' hv'φ (u j) (w j) (hw j) (g j)
      (by rw [← Category.assoc, hg j, Category.assoc, hu₂ j])
  have hA := GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1
  have htan : ∀ j, IsTangent (g j) := fun j => hA.2.1 _ _ (hcomb j)
  have hB := GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ g htan
  obtain ⟨w'', hw''⟩ := (hB.1 (C ρ i)).exists
  have hleft : w''.left ≫ m1'.φ = y'.u ρ i :=
    comb_left_of_isCombAt m1' (yT.u ρ) (C ρ i) _ (hchg.2.1 ρ i) g hg1 w'' hw''
  refine ⟨w'', m1'.cart.1.hom_ext (by rw [hleft, hu''1]) (by rw [Over.w w'', hu''0]; rfl), ?_⟩
  exact hA.2.2.1 _ (fun j k => iK (u j k)) g (C ρ i) w'' hcomb hw''

end GlobalTheory.PtDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMemLatDbl
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacEigen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) : AddSubgroup (Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) where
  carrier := {z | z.toCols₁ ∈ latAtV X W v ∧ z.toCols₂ ∈ latAtV X W v}
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem (latAtV X W v), zero_mem (latAtV X W v)⟩
  neg_mem' := fun {a} ha => ⟨neg_mem ha.1, neg_mem ha.2⟩

theorem mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) (z : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) :
    z ∈ latDbl X W v ↔ z.toCols₁ ∈ latAtV X W v ∧ z.toCols₂ ∈ latAtV X W v := Iff.rfl

theorem fromCols_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {γ₁ γ₂ : Matrix (Fin n) (Fin d) (AE F E)}
    (h₁ : γ₁ ∈ latAtV X W v) (h₂ : γ₂ ∈ latAtV X W v) : Matrix.fromCols γ₁ γ₂ ∈ latDbl X W v := by
  rw [mem_latDbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]
  exact ⟨h₁, h₂⟩

theorem at_of_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {z : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)}
    (hz : z ∈ latDbl X W v) : At (evFin F v) z := by
  intro u hu
  have h1 := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 _ hz.1 u hu
  have h2 := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 _ hz.2 u hu
  ext i (j | j)
  · simpa using congrFun (congrFun h1 i) j
  · simpa using congrFun (congrFun h2 i) j

end GlobalTheory.DblVacEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIntegralTangentInSpanLieBasis
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory GlobalTheory.CM GlobalTheory.LamT
namespace GlobalTheory.PtDeg.LieModel

theorem isGrpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (G := G) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

theorem dualMap_id (R : Type) [CommRing R] : dualMap (RingHom.id R) = RingHom.id (DualNumber R) := by
  apply RingHom.ext
  intro x
  ext <;> simp [dualMap]

theorem spMap_dualMap_id (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  rw [dualMap_id]; exact Spec.map_id _

theorem spMap_comp_two {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

theorem generic_coords_in_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G)) (M : Fin F.P₀.g → Fin F.P₀.g → K), IsLieBasis vV → (∀ k, ∃ w : epsR K ⟶ F.P₀.A, IsLieComb (M k) F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ) → ∀ (ub : epsOver T.V T.V ⟶ G.t.G) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), IsTan ub → u'' ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ ub.left → ∃ (a : Fin F.P₀.g → T.V) (w'' : epsR T.Fr ⟶ t'.G), w''.left = u'' ∧ IsLieComb (∑ k, algebraMap T.V T.Fr (a k) • fun l => iK (M k l)) v' w'' := by
  intro E _ _ _ H K _ _ B t₀ m2 F T iK ρV hρV G t' n n' m2' h2 v' hv' hv'φ vV M hvV hM ub u'' hub hu''

  let ub' : epsR T.V ⟶ G.t.G := Over.homMk ub.left (Over.w ub)
  have hub' : IsTangent ub' := by
    unfold IsTangent
    refine hub.trans ?_
    have e : (1 : ptOver T.V T.V ⟶ G.t.G) = toUnit _ ≫ η[G.t.G] := rfl
    rw [e, Over.comp_left]
    have e2 : (toUnit (ptOver T.V T.V)).left = 𝟙 (Sp T.V) := by
      have := Over.w (toUnit (ptOver T.V T.V))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact Category.id_comp _
  obtain ⟨a, ha, -⟩ := hvV.2 ub' hub'

  have hw'' : u'' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    apply spMap_frac_cancel (V := T.V)
    rw [Category.assoc, ← m2'.cart.1.w, ← Category.assoc, hu'', Category.assoc, Over.w ub]
    show spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap (algebraMap T.V (DualNumber T.V)) = _
    exact (spMap_comp_two _ _).trans ((congrArg spMap (dualMap_alg _)).trans (spMap_comp_two _ _).symm)

  have hsq : ∀ k, (spMap (dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left) ≫ G.t.G.hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := fun k => by
    rw [Category.assoc, Over.w (vV k)]
    exact (spMap_comp_two _ _).trans ((congrArg spMap (dualMap_alg _)).trans (spMap_comp_two _ _).symm)
  let g : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G) := fun k =>
    Over.homMk (m2'.cart.1.lift _ _ (hsq k)) (m2'.cart.1.lift_snd _ _ _)
  have hg1 : ∀ k, (g k).left ≫ m2'.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left :=
    fun k => m2'.cart.1.lift_fst _ _ _
  have hB : IsGrpPullback t'.G B.t.G (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) (n'.φ ≫ m2.φ) :=
    n'.cart.comp m2.cart
  have hT' := LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1
  have hgk : ∀ k, IsLieComb (fun l => iK (M k l)) v' (g k) := by
    intro k
    obtain ⟨wk, hwk, hwkeq⟩ := hM k
    obtain ⟨w₁, hw₁, -⟩ := hT'.1 (fun l => iK (M k l))
    have hf : spMap (RingHom.id T.Fr) ≫ (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) =
        spMap iK ≫ spMap (algebraMap (𝓞 K) K) := by rw [spMap_id', Category.id_comp]
    have hm := LetterInt.comb_match hB F.fib.2.1 (RingHom.id T.Fr) iK hf
      (fun i => by rw [spMap_dualMap_id, Category.id_comp]; exact hv'φ i) (fun _ => rfl) hw₁ hwk
    rw [spMap_dualMap_id, Category.id_comp] at hm
    have he : w₁ = g k := by
      refine Over.OverMorphism.ext (hB.1.hom_ext ?_ ((Over.w w₁).trans (Over.w (g k)).symm))
      rw [hm, ← hwkeq, ← h2, ← Category.assoc (g k).left, hg1, Category.assoc]
    exact he ▸ hw₁

  have hgt : ∀ k, IsTangent (g k) := fun k => hT'.2.1 _ _ (hgk k)
  obtain ⟨w, hw, -⟩ := (LieComb.lieComb_algebra T.Fr t'.G _ g hgt).1 (fun k => algebraMap T.V T.Fr (a k))
  have hcomb := hT'.2.2.1 _ (fun k l => iK (M k l)) g _ w hgk hw
  have hf2 : spMap (algebraMap T.V T.Fr) ≫ 𝟙 (Sp T.V) = spMap (RingHom.id T.Fr) ≫ spMap (algebraMap T.V T.Fr) := by
    rw [spMap_id', Category.id_comp, Category.comp_id]
  have hm2 := LetterInt.comb_match (isGrpPullback_self G.t.G) m2'.cart (algebraMap T.V T.Fr) (RingHom.id T.Fr) hf2
    (v₁ := vV) (v₂ := g) (fun i => by rw [spMap_dualMap_id, Category.id_comp, Category.comp_id, hg1])
    (c₁ := a) (c₂ := fun k => algebraMap T.V T.Fr (a k)) (fun _ => rfl) ha hw
  rw [spMap_dualMap_id, Category.id_comp, Category.comp_id] at hm2
  have hleft : w.left = u'' := by
    refine m2'.cart.1.hom_ext ?_ ((Over.w w).trans hw''.symm)
    rw [← hm2, hu'']
    rfl
  exact ⟨a, w, hleft, hcomb⟩

end GlobalTheory.PtDeg.LieModel
end

