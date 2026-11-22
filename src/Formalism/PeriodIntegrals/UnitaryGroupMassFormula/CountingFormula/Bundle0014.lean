import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0012
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0013
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameDeterminant.DdSNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseMulEquiv

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGSB
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

theorem count_bijection : CountBij := by
  intro F E _ _ _ _ _ _ _ M hl _ e hes hO V _ _ H Λ π Ph hπ ϖ hϖ ι _ _ G₀ h1 h2 h3
  haveI := hl
  have hπa := hπ.1
  have hπL := hπ.2.1
  let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let lift : (Fin (Module.finrank E V) → 𝓀[F]) → (Fin (Module.finrank E V) → 𝓀[F]) → V := fun X1 Y1 =>
    π.symm ((fun k => liftF F (X1 k)), fun k => liftF F (Y1 k))
  have hlift : ∀ X1 Y1, π (lift X1 Y1) = ((fun k => liftF F (X1 k)), fun k => liftF F (Y1 k)) :=
    fun _ _ => AddEquiv.apply_symm_apply _ _
  have hliftL : ∀ X1 Y1, lift X1 Y1 ∈ Λ := fun X1 Y1 =>
    (hπL _).2 (by rw [hlift]; exact ⟨fun k => liftF_mem F _, fun k => liftF_mem F _⟩)
  have hred1 : ∀ X1 Y1 k, resF F ((π (lift X1 Y1)).1 k) = X1 k := by
    intro X1 Y1 k; rw [hlift]; exact resF_liftF F _
  have hred2 : ∀ X1 Y1 k, resF F ((π (lift X1 Y1)).2 k) = Y1 k := by
    intro X1 Y1 k; rw [hlift]; exact resF_liftF F _
  let Gm : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝓀[F] := Matrix.of fun i j => resF F ((e (G₀ (σ.symm j) (σ.symm i))).1)
  let Ph' := Ph.map (IsLocalRing.residue 𝒪[F])
  let g : (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) × (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) →
      (ι → V ⧸ H.smulLat (algebraMap F E (ϖ : F)) Λ) := fun XY a =>
    Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (lift (XY.1 (σ a)) (XY.2 (σ a)))
  let S : Set ((Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) × (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F])) :=
    {XY | LinearIndependent 𝓀[F] XY.1 ∧ LinearIndependent 𝓀[F] XY.2 ∧
      ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph' k l * XY.2 j l = Gm i j}
  have hL := fun (v : ι → V) (hv : ∀ a, v a ∈ Λ) a => (hπL (v a)).1 (hv a)
  have hR : Set.range (fun v : {v : ι → V // H.Prim Λ v ∧ ∀ a b,
      H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
      fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (v.1 a)) = g '' S := by
    ext c
    constructor
    · rintro ⟨⟨v, hP, hG⟩, rfl⟩
      have hv : ∀ a, v a ∈ Λ := hP.1
      have hpr := (prim_iff e hO H Λ π hπa hπL hϖ v hv).1 hP
      have hgr := (gram_iff e hes hO H Λ π Ph hπ hϖ G₀ h1 h2 v hv).1 hG
      refine ⟨((fun i k => resF F ((π (v (σ.symm i))).1 k)), fun i k => resF F ((π (v (σ.symm i))).2 k)),
        ⟨hpr.1.comp σ.symm σ.symm.injective, hpr.2.comp σ.symm σ.symm.injective, ?_⟩, ?_⟩
      · intro i j
        have := hgr (σ.symm j) (σ.symm i)
        rw [resF_bil _ _ (hL v hv _).1 (hL v hv _).2 Ph] at this
        exact this
      · funext a
        show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
        rw [mk_eq_iff e H Λ π hπa hπL hϖ (hliftL _ _) (hv a)]
        refine ⟨fun k => ?_, fun k => ?_⟩
        · rw [hred1]; simp
        · rw [hred2]; simp
    · rintro ⟨XY, ⟨hX, hY, hE⟩, rfl⟩
      let v : ι → V := fun a => lift (XY.1 (σ a)) (XY.2 (σ a))
      have hv : ∀ a, v a ∈ Λ := fun a => hliftL _ _
      have hr1 : (redM F fun a => (π (v a)).1) = XY.1 ∘ σ := by
        funext a k; exact hred1 _ _ k
      have hr2 : (redM F fun a => (π (v a)).2) = XY.2 ∘ σ := by
        funext a k; exact hred2 _ _ k
      have hP : H.Prim Λ v := (prim_iff e hO H Λ π hπa hπL hϖ v hv).2
        ⟨by rw [hr1]; exact hX.comp σ σ.injective, by rw [hr2]; exact hY.comp σ σ.injective⟩
      have hG := (gram_iff e hes hO H Λ π Ph hπ hϖ G₀ h1 h2 v hv).2 (by
        intro a b
        rw [resF_bil _ _ (hL v hv _).1 (hL v hv _).2 Ph]
        have := hE (σ b) (σ a)
        simp only [Gm, Matrix.of_apply, Equiv.symm_apply_apply] at this
        rw [← this]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [hred1, hred2]
        rfl)
      exact ⟨⟨v, hP, hG⟩, rfl⟩
  have hinj : Set.InjOn g S := by
    intro XY _ XY' _ heq
    have hc : ∀ a, (∀ k, XY.1 (σ a) k = XY'.1 (σ a) k) ∧ ∀ k, XY.2 (σ a) k = XY'.2 (σ a) k := by
      intro a
      have := (mk_eq_iff e H Λ π hπa hπL hϖ (hliftL _ _) (hliftL _ _)).1 (congrFun heq a)
      simp only [hred1, hred2] at this
      exact this
    refine Prod.ext (funext fun i => funext fun k => ?_) (funext fun i => funext fun k => ?_)
    · have := (hc (σ.symm i)).1 k
      simpa using this
    · have := (hc (σ.symm i)).2 k
      simpa using this

  have hrank : Gm.rank = Fintype.card ι := by
    let A : Matrix ι ι 𝒪[F] := Matrix.of fun a b => ⟨(e (G₀ a b)).1, ((hO _).1 (h1 a b)).1⟩
    let φ : E →+* F := (RingHom.fst F F).comp (e : E →+* F × F)
    have hA : ((A.det : 𝒪[F]) : F) = φ G₀.det := by
      rw [← 𝒪[F].coe_subtype, RingHom.map_det, RingHom.map_det]
      congr 1
    obtain ⟨y, hy, hdy⟩ := h3
    have hyO := ((hO y).1 hy).1
    have hAu : IsUnit A.det := by
      refine isUnit_iff_exists_inv.2 ⟨⟨_, hyO⟩, Subtype.ext ?_⟩
      rw [Subring.coe_mul, hA]
      have := congrArg φ hdy
      rw [map_mul, map_one] at this
      simpa [φ] using this
    have hGm : Gm = Matrix.reindex σ σ (A.map (IsLocalRing.residue 𝒪[F])).transpose := by
      ext i j
      simp only [Gm, A, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
        Matrix.map_apply]
      rw [← resF_coe]
    rw [Matrix.rank_of_isUnit Gm ?_, Fintype.card_fin]
    rw [Matrix.isUnit_iff_isUnit_det, hGm, Matrix.det_reindex_self, Matrix.det_transpose]
    have : (A.map (IsLocalRing.residue 𝒪[F])) = (IsLocalRing.residue 𝒪[F]).mapMatrix A := rfl
    rw [this, ← RingHom.map_det]
    exact hAu.map _
  refine ⟨Gm, hrank, ?_⟩
  have hq : (Nat.card 𝓀[F] : ℝ) ≠ 0 := by
    have : 0 < Nat.card 𝓀[F] := Nat.card_pos
    exact_mod_cast this.ne'
  unfold Loc.HermSp.dens
  rw [div_mul_cancel₀ _ (zpow_ne_zero _ hq), hR, Nat.card_coe_set_eq, hinj.ncard_image]
  rfl

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GramCondIff
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel
open Classical

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

theorem span_pi_iff (hR : RedData ϖ k r n b Λ) (x : M.L.O) :
    (x : E) ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔ r x = 0 := by
  rw [Submodule.mem_span_singleton, hR.ker]
  constructor
  · rintro ⟨o, ho⟩
    exact ⟨o, o.2, by rw [← ho]; show (o : E) * _ = _; ring⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨⟨z, hz⟩, by rw [hzx]; show z * _ = _; ring⟩

theorem cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars 𝒪[F])

def Ph (r : M.L.O →+* k) (H : Loc.HermSp M V) (b : Fin n → V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O) :
    Matrix (Fin n) (Fin n) k := fun i j => r ⟨H.h (b i) (b j), hint i j⟩

theorem gram_mem (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    H.h x y = ∑ i, ∑ j, cO hR x i * M.L.cj (cO hR y j) * H.h (b i) (b j) ∧ H.h x y ∈ M.L.O := by
  have he : H.h x y = ∑ i, ∑ j, cO hR x i * M.L.cj (cO hR y j) * H.h (b i) (b j) := by
    conv_lhs => rw [cO_sum hR hx, cO_sum hR hy]
    exact h_expand H b _ _
  refine ⟨he, ?_⟩
  rw [he]
  exact M.L.O.sum_mem fun i _ => M.L.O.sum_mem fun j _ =>
    M.L.O.mul_mem (M.L.O.mul_mem (cO_mem hR x i) (cj_mem (cO_mem hR y j))) (hint i j)

theorem gram_red (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    (q : ℕ) (rfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ q)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    r ⟨H.h x y, (gram_mem hR H hint hx hy).2⟩ =
      ∑ i, ∑ j, red hR x i * Ph r H b hint i j * red hR y j ^ q := by
  have h1 : (⟨H.h x y, (gram_mem hR H hint hx hy).2⟩ : M.L.O) =
      ∑ i, ∑ j, (⟨cO hR x i, cO_mem hR x i⟩ : M.L.O) * ⟨M.L.cj (cO hR y j), cj_mem (cO_mem hR y j)⟩ *
        ⟨H.h (b i) (b j), hint i j⟩ := by
    apply Subtype.ext
    show H.h x y = _
    rw [(gram_mem hR H hint hx hy).1]
    push_cast
    rfl
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, rfrob ⟨cO hR y j, cO_mem hR y j⟩ ⟨M.L.cj (cO hR y j), cj_mem (cO_mem hR y j)⟩ rfl]
  simp only [red, Ph]
  ring

theorem gram_cond_iff (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V)
    (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    (q : ℕ) (rfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ q)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) (g : E) (hg : g ∈ M.L.O) :
    H.h x y - g ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔
      ∑ i, ∑ j, red hR x i * Ph r H b hint i j * red hR y j ^ q = r ⟨g, hg⟩ := by
  have hm := (gram_mem hR H hint hx hy).2
  have := span_pi_iff hR ⟨H.h x y - g, M.L.O.sub_mem hm hg⟩
  simp only at this
  rw [this, show (⟨H.h x y - g, M.L.O.sub_mem hm hg⟩ : M.L.O) = ⟨H.h x y, hm⟩ - ⟨g, hg⟩ from
    Subtype.ext rfl, map_sub, sub_eq_zero, gram_red hR H hint q rfrob hx hy]

end FC

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.HTIntLeft
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem inW_add (D : Formalism.BasicNotions.D7) {x y : (VS D).V} (hx : InW D x) (hy : InW D y) : InW D (x + y) := by
  unfold InW at *
  obtain ⟨h1, h2, h3⟩ := hx
  obtain ⟨k1, k2, k3⟩ := hy
  exact ⟨fun a => by rw [map_add, h1 a, k1 a, add_zero], fun a => by rw [map_add, h2 a, k2 a, add_zero],
    by rw [map_add, h3, k3, add_zero]⟩

theorem inW_smul (D : Formalism.BasicNotions.D7) (k : D.host.E) {x : (VS D).V} (hx : InW D x) : InW D (k • x) := by
  unfold InW at *
  obtain ⟨h1, h2, h3⟩ := hx
  exact ⟨fun a => by rw [map_smul, h1 a, smul_zero], fun a => by rw [map_smul, h2 a, smul_zero],
    by rw [map_smul, h3, smul_zero]⟩

theorem inW_zero (D : Formalism.BasicNotions.D7) : InW D 0 := by
  unfold InW
  exact ⟨fun a => map_zero _, fun a => map_zero _, map_zero _⟩

theorem inW_sum (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (x : ι → (VS D).V) (hx : ∀ i, InW D (x i)) :
    InW D (∑ i ∈ s, x i) := by
  exact Finset.sum_induction x (InW D) (fun a b ha hb => inW_add D ha hb) (inW_zero D) (fun i _ => hx i)

def LamW (D : Formalism.BasicNotions.D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V where
  carrier := {y | y ∈ Λ ∧ InW D y}
  add_mem' hx hy := ⟨Λ.add_mem hx.1 hy.1, inW_add D hx.2 hy.2⟩
  zero_mem' := ⟨Λ.zero_mem, inW_zero D⟩
  smul_mem' o _ hx := ⟨Λ.smul_mem o hx.1, by
    rw [← algebraMap_smul D.host.E o]; exact inW_smul D _ hx.2⟩

theorem hT_int_left (D : Formalism.BasicNotions.D7) (n : ℤ) (x y : (VS D).V) :
    (VS D).hT ((n : D.host.E) • x) y = (n : D.host.E) * (VS D).hT x y := by
  rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply, star_intCast]

private theorem hT_isIntegral_of_mem_unimodular (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {y v : (VS D).V} (hy : y ∈ Λ) (hv : v ∈ Λ) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (VS D).hT y v := by
  have h : Formalism.E.hdual (VS D).hT Λ = Λ := hU
  have hv' : v ∈ Formalism.E.hdual (VS D).hT Λ := by rw [h]; exact hv
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hv'
  exact Submodule.mem_one.mp (hv' y hy)

theorem pW_lat (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (heΛ : ∀ a, D.sp.hypE a ∈ Λ) (d : ℤ)
    (hdF : ∀ a, (d : D.host.E) • D.sp.hypF a ∈ Λ)
    (hdz : ((d : D.host.E) * (D.sp.T : D.host.E)⁻¹) • D.sp.zm ∈ Λ) {v : (VS D).V} (hv : v ∈ Λ) :
    (d : D.host.E) ^ 2 • pW D v ∈ Λ := by
  have hT0 : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr D.sp.T_prime.ne_zero
  have hsm : ∀ (o : 𝓞 D.host.E) {y : (VS D).V}, y ∈ Λ → algebraMap (𝓞 D.host.E) D.host.E o • y ∈ Λ :=
    fun o y hy => by rw [algebraMap_smul]; exact Λ.smul_mem o hy
  have hint : ∀ (n : ℤ) {y : (VS D).V}, y ∈ Λ → (n : D.host.E) • y ∈ Λ := fun n y hy => by
    have := hsm (n : 𝓞 D.host.E) hy; rwa [map_intCast] at this
  have hnat : ∀ (n : ℕ) {y : (VS D).V}, y ∈ Λ → (n : D.host.E) • y ∈ Λ := fun n y hy => by
    have := hsm (n : 𝓞 D.host.E) hy; rwa [map_natCast] at this
  unfold pW
  simp only [smul_add, smul_sub, Finset.smul_sum]
  refine Λ.add_mem (Λ.sub_mem (Λ.sub_mem ?_ ?_) ?_) ?_
  · rw [pow_two, mul_smul]; exact hint d (hint d hv)
  · refine Λ.sum_mem (fun a _ => ?_)
    obtain ⟨o, ho⟩ := hT_isIntegral_of_mem_unimodular D hU (hdF a) hv
    have heq : (d : D.host.E) ^ 2 • ((VS D).hT (D.sp.hypF a) v • D.sp.hypE a) =
        algebraMap (𝓞 D.host.E) D.host.E ((d : 𝓞 D.host.E) * o) • D.sp.hypE a := by
      simp only [smul_smul]
      rw [map_mul, map_intCast, ho, hT_int_left]
      congr 1
      ring
    rw [heq]; exact hsm _ (heΛ a)
  · refine Λ.sum_mem (fun a _ => ?_)
    obtain ⟨o, ho⟩ := hT_isIntegral_of_mem_unimodular D hU (heΛ a) hv
    have heq : (d : D.host.E) ^ 2 • ((VS D).hT (D.sp.hypE a) v • D.sp.hypF a) =
        algebraMap (𝓞 D.host.E) D.host.E ((d : 𝓞 D.host.E) * o) • ((d : D.host.E) • D.sp.hypF a) := by
      simp only [smul_smul]
      rw [map_mul, map_intCast, ho]
      congr 1
      ring
    rw [heq]; exact hsm _ (hdF a)
  · obtain ⟨o, ho⟩ := hT_isIntegral_of_mem_unimodular D hU hdz hv
    have hc : (VS D).hT (((d : D.host.E) * (D.sp.T : D.host.E)⁻¹) • D.sp.zm) v =
        (d : D.host.E) * (D.sp.T : D.host.E)⁻¹ * (VS D).hT D.sp.zm v := by
      rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
      congr 1
      simp
    have hdzm : (d : D.host.E) • D.sp.zm ∈ Λ := by
      have := hnat D.sp.T hdz
      rwa [smul_smul, ← mul_assoc, mul_comm (D.sp.T : D.host.E) (d : D.host.E), mul_assoc,
        mul_inv_cancel₀ hT0, mul_one] at this
    have heq : (d : D.host.E) ^ 2 • (((VS D).hT D.sp.zm v / (D.sp.T : D.host.E)) • D.sp.zm) =
        algebraMap (𝓞 D.host.E) D.host.E o • ((d : D.host.E) • D.sp.zm) := by
      simp only [smul_smul]
      rw [ho, hc]
      congr 1
      rw [div_eq_mul_inv]
      ring
    rw [heq]; exact hsm _ hdzm

def Pm (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  1 - R * betaZ D Z

theorem beta_Pm (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (hR : betaZ D Z * R = 1) : betaZ D Z * Pm D Z R = 0 := by
  unfold Pm
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hR, Matrix.one_mul, sub_self]

def Gfl (D : Formalism.BasicNotions.D7) (T' : D.host.E) (b1 b2 : Fin (D.R.rS + 1)) : D.host.E :=
  if b1 = Fin.last D.R.rS ∧ b2 = Fin.last D.R.rS then -T' else 0

def gam (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E) (c0 : D.host.E)
    (b : Fin (D.R.rS + 1)) : D.host.E :=
  (∑ b', Pm D Z R b' b * (Z (Fin.last D.R.rS) b' / star c0)) / (D.sp.T : D.host.E)

def kap (D : Formalism.BasicNotions.D7) (T' : D.host.E) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (c0 : D.host.E) (b : Fin (D.R.rS + 1)) : D.host.E :=
  (∑ b1, ∑ b2, star (Pm D Z R b1 b) * Pm D Z R b2 b * Gfl D T' b1 b2) +
    (D.sp.T : D.host.E) * star (gam D Z R c0 b) * gam D Z R c0 b

def tv (D : Formalism.BasicNotions.D7) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (x : (Fin D.R.rS → (VS D).V) × (VS D).V) (b : Fin (D.R.rS + 1)) : (VS D).V :=
  ∑ b', Pm D Z R b' b • pWf D x b'

private theorem hT_swap_eq_star' (D : Formalism.BasicNotions.D7) (p q : (VS D).V) :
    (VS D).hT q p = star ((VS D).hT p q) := by
  first
  | exact ((VS D).herm p q).symm
  | exact ((VS D).herm.eq p q).symm
  | simpa using ((VS D).herm p q).symm
  | simpa using ((VS D).herm.eq p q).symm

private theorem pW_add' (D : Formalism.BasicNotions.D7) (u v : (VS D).V) : pW D (u + v) = pW D u + pW D v := by
  unfold pW
  simp only [map_add, add_smul, Finset.sum_add_distrib, add_div]
  abel

private theorem pW_smul' (D : Formalism.BasicNotions.D7) (c : D.host.E) (v : (VS D).V) :
    pW D (c • v) = c • pW D v := by
  unfold pW
  simp only [map_smul, smul_eq_mul, mul_div_assoc, mul_smul, smul_sub, smul_add, Finset.smul_sum]

private theorem pW_sum' (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (f : ι → (VS D).V) :
    pW D (∑ i ∈ s, f i) = ∑ i ∈ s, pW D (f i) := by
  exact map_sum (AddMonoidHom.mk' (pW D) (pW_add' D)) f s

private theorem hT_pW_self_of_hT_hypE_eq_zero (D : Formalism.BasicNotions.D7) (w : (VS D).V)
    (hw : ∀ a, (VS D).hT (D.sp.hypE a) w = 0) :
    (VS D).hT (pW D w) (pW D w) = (VS D).hT w w +
      (D.sp.T : D.host.E) * star ((VS D).hT D.sp.zm w / (D.sp.T : D.host.E)) *
        ((VS D).hT D.sp.zm w / (D.sp.T : D.host.E)) := by
  have hs : ∀ p q : (VS D).V, (VS D).hT q p = star ((VS D).hT p q) := fun p q => hT_swap_eq_star' D p q
  have hee : ∀ a a', (VS D).hT (D.sp.hypE a) (D.sp.hypE a') = 0 := D.sp.hyp_ee
  have hze : ∀ a, (VS D).hT D.sp.zm (D.sp.hypE a) = 0 := fun a => (D.sp.hyp_orthz a).1
  have hez : ∀ a, (VS D).hT (D.sp.hypE a) D.sp.zm = 0 := fun a => by rw [hs, hze, star_zero]
  have hwe : ∀ a, (VS D).hT w (D.sp.hypE a) = 0 := fun a => by rw [hs, hw a, star_zero]
  have hzz : (VS D).hT D.sp.zm D.sp.zm = -(D.sp.T : D.host.E) := D.sp.zm_norm
  have hT0 : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr D.sp.T_prime.ne_zero
  have hwz : (VS D).hT w D.sp.zm = star ((VS D).hT D.sp.zm w) := hs _ _
  unfold pW
  simp only [hw, zero_smul, Finset.sum_const_zero, sub_zero]
  set g := (VS D).hT D.sp.zm w / (D.sp.T : D.host.E) with hg
  set s := ∑ a, (VS D).hT (D.sp.hypF a) w • D.sp.hypE a with hsdef
  have hsy : ∀ y, (VS D).hT s y = ∑ a, star ((VS D).hT (D.sp.hypF a) w) * (VS D).hT (D.sp.hypE a) y := by
    intro y
    simp only [hsdef, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂]
  have hys : ∀ y, (VS D).hT y s = ∑ a, (VS D).hT (D.sp.hypF a) w * (VS D).hT y (D.sp.hypE a) := by
    intro y
    simp only [hsdef, map_sum, map_smul, smul_eq_mul]
  have h1 : (VS D).hT s w = 0 := by rw [hsy]; simp [hw]
  have h2 : (VS D).hT s s = 0 := by rw [hsy]; simp [hys, hee]
  have h3 : (VS D).hT s D.sp.zm = 0 := by rw [hsy]; simp [hez]
  have h4 : (VS D).hT w s = 0 := by rw [hys]; simp [hwe]
  have h5 : (VS D).hT D.sp.zm s = 0 := by rw [hys]; simp [hze]
  have h6 : (VS D).hT D.sp.zm w = (D.sp.T : D.host.E) * g := by
    rw [hg, mul_div_assoc', mul_comm, mul_div_assoc, div_self hT0, mul_one]
  simp only [map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, h1, h2, h3, h4, h5, hzz, hwz, h6,
    starRingEnd_apply, star_mul', star_natCast]
  ring

theorem tv_norm (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D) (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E)
    (hR : betaZ D Z * R = 1) (he : F0.e = D.sp.hypE) {c0 : D.host.E} (hc0 : c0 ≠ 0) (hz : F0.z = c0 • D.sp.zm)
    {x : (Fin D.R.rS → (VS D).V) × (VS D).V} (hx : Good D T' F0 Λ Z x) (b : Fin (D.R.rS + 1)) :
    (VS D).hT (tv D Z R x b) (tv D Z R x b) = kap D T' Z R c0 b := by
  obtain ⟨-, hZ, hG⟩ := hx
  set w := ∑ b', Pm D Z R b' b • fr D x b' with hw
  have htv : tv D Z R x b = pW D w := by
    show ∑ b', Pm D Z R b' b • pW D (fr D x b') = pW D w
    rw [hw, pW_sum']
    simp only [pW_smul']
  have hEu : ∀ a b', (VS D).hT (D.sp.hypE a) (fr D x b') = Z (Fin.castSucc a) b' := by
    intro a b'
    have h := hZ (Fin.castSucc a) b'
    simpa [brS, FlagG.fvec, he] using h
  have hzu : ∀ b', (VS D).hT D.sp.zm (fr D x b') = Z (Fin.last D.R.rS) b' / star c0 := by
    intro b'
    have h := hZ (Fin.last D.R.rS) b'
    simp only [brS, FlagG.fvec, Fin.snoc_last, hz, LinearMap.map_smulₛₗ₂, smul_eq_mul,
      starRingEnd_apply] at h
    rw [eq_div_iff (star_ne_zero.mpr hc0), ← h, mul_comm]
  have hGu : ∀ b1 b2, (VS D).hT (fr D x b1) (fr D x b2) = Gfl D T' b1 b2 := by
    intro b1 b2
    rw [hG b1 b2]
    unfold Gfl
    split_ifs <;> first | rfl | (exfalso; tauto)
  have hEw : ∀ a, (VS D).hT (D.sp.hypE a) w = 0 := by
    intro a
    have h0 : (betaZ D Z * Pm D Z R) a b = 0 := by rw [beta_Pm D Z R hR]; rfl
    rw [Matrix.mul_apply] at h0
    rw [hw, map_sum]
    simp only [map_smul, smul_eq_mul, hEu]
    simpa [betaZ, Matrix.submatrix_apply, mul_comm] using h0
  have hww : (VS D).hT w w =
      ∑ b1, ∑ b2, star (Pm D Z R b1 b) * Pm D Z R b2 b * Gfl D T' b1 b2 := by
    rw [hw]
    simp only [LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂, map_sum, map_smul, map_smulₛₗ,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b1 _ => Finset.sum_congr rfl (fun b2 _ => ?_))
    rw [hGu b1 b2]
    ring
  have hzw : (VS D).hT D.sp.zm w = ∑ b', Pm D Z R b' b * (Z (Fin.last D.R.rS) b' / star c0) := by
    rw [hw, map_sum]
    simp only [map_smul, smul_eq_mul, hzu]
  rw [htv, hT_pW_self_of_hT_hypE_eq_zero D w hEw]
  unfold kap gam
  rw [hww, hzw]

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepGood
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_mem_ddS_zpow (D : Formalism.BasicNotions.D7) (k : ℕ) :
    (1 : D.host.E) ∈ ((ddS D) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have h0 : ddS D ≠ 0 := PI.TripleFrameDeterminant.W.ddS_ne_zero D
  have hle : ddS D ^ k ≤ 1 := by
    rw [ddS, ← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one
  have h := FractionalIdeal.inv_anti_mono (pow_ne_zero k h0) one_ne_zero hle
  rw [inv_one] at h
  rw [zpow_neg, zpow_natCast]
  exact h (FractionalIdeal.one_mem_one _)

theorem flag_gram (D : Formalism.BasicNotions.D7) {T' : D.host.E} (G : FlagG (VS D) D.R.rS T') (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (G.fvec a) (G.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T' else 0 := by
  have hs : ∀ x y, (VS D).hT y x = starRingEnd D.host.E ((VS D).hT x y) :=
    fun x y => ((VS D).herm.eq x y).symm
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, G.z_norm]
    | cast j =>
      rw [hs]
      simp [FlagG.fvec, G.z_orth j]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, G.z_orth i]
    | cast j => simp [FlagG.fvec, G.e_iso i j]

theorem good_places_integral : GoodEZ := by
  intro D T T' F0 Λ Z F' hF'
  obtain ⟨hT, -, -, hFr, hZ⟩ := hF'
  have hfr : fr D (F'.fl.e, F'.fl.z) = F'.fl.fvec := rfl
  refine ⟨fun b => ?_, fun a b => ?_, fun a b => ?_⟩
  · rw [hfr]
    have h := PI.CntNotIntW.frame_mem Λ F' hFr.2 hT.1.1 b 1 (one_mem_ddS_zpow D _)
    rwa [one_smul] at h
  · rw [hfr, ← hZ]
    rfl
  · rw [hfr]
    exact flag_gram D F'.fl a b

end PI.UnitaryGroupMassFormula.CntFormula
end
end

