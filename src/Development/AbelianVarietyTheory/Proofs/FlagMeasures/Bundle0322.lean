import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0303
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeUnimodularAndPrimitive
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsEqOfStabilizerConjugateLattices
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0310
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardLatticeDualVectorsChangeUnipotent
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalHyperbolicFrameAnisotropicMemSpanTrans
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St
variable {D : D7}

theorem crd_sum_smul (X : HidaSetting D) {ι : Type} [Fintype ι] (c : ι → X.B.I.E) (v : ι → (VS D).V) :
    X.crd (∑ k, X.ιE (c k) • v k) = fun i => ∑ k, c k * X.crd (v k) i := by
  funext i
  simp [HidaSetting.crd, crdOf, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_mul]

theorem crd_injective (X : HidaSetting D) : Function.Injective X.crd := by
  intro v w h
  apply X.bas.repr.injective
  ext i
  have := congrFun h i
  simp only [HidaSetting.crd, crdOf] at this
  rw [X.ιE.symm.injective this]

theorem orth_mem_span_qFr : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    WittX X u wt → ∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) →
    (VS D).hT (X.zu u) y = 0 → ∃ d : Fin (D.R.N 0) → D.host.E, Fintype.linearCombination D.host.E (qFr wt) d = y := by
  intro D X u wt hw y hef hz
  classical
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hq, he, hf, hzc, -, -⟩ := qFrame_basis_gram D X u wt hw
  have hcol : ∀ k i, Q i k = X.crd (famQ X u wt k) i := by
    rintro (j | a | a | ⟨⟩) i
    · simp [famQ, hq]
    · simp [famQ, he, HidaSetting.eR]
    · simp [famQ, hf, HidaSetting.fR]
    · simp [famQ, hzc, HidaSetting.zR]
  set c := Qi *ᵥ X.crd y with hc
  have hy : y = ∑ k, X.ιE (c k) • famQ X u wt k := by
    apply crd_injective X
    rw [crd_sum_smul]
    have : Q *ᵥ c = X.crd y := by rw [hc, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    rw [← this]
    funext i
    simp only [Matrix.mulVec, dotProduct, hcol]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hy
  simp only [famQ, Sum.elim_inl, Sum.elim_inr, Fintype.univ_unit, Finset.sum_singleton] at hy
  have hqe : ∀ j b, (VS D).hT (X.eX b) (qFr wt j) = 0 := fun j b =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inl b))
  have hqf : ∀ j b, (VS D).hT (X.fY b) (qFr wt j) = 0 := fun j b =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inr (Sum.inl b)))
  have hqz : ∀ j, (VS D).hT (X.zu u) (qFr wt j) = 0 := fun j =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inr (Sum.inr ())))

  have c2 : ∀ b, X.ιE (c (Sum.inr (Sum.inr (Sum.inl b)))) = 0 := by
    intro b
    have h := (hef b).1
    rw [hy] at h
    simpa [map_add, map_sum, hqe, X.ee, X.ef, (X.zu_orth u b).1] using h
  have c1 : ∀ b, X.ιE (c (Sum.inr (Sum.inl b))) = 0 := by
    intro b
    have h := (hef b).2
    rw [hy] at h
    simpa [map_add, map_sum, hqf, X.ff, hT_fe, (X.zu_orth u b).2] using h
  have c3 : X.ιE (c (Sum.inr (Sum.inr (Sum.inr ())))) = 0 := by
    have h := hz
    rw [hy] at h
    simp [map_add, map_sum, hqz, hT_ze, hT_zf] at h
    rw [h.resolve_right (hT_zz_ne X u), map_zero]
  refine ⟨fun j => X.ιE (c (Sum.inl j)), ?_⟩
  rw [hy, Fintype.linearCombination_apply]
  simp [c1, c2, c3]

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairIsScalarInUnipotentRadicalDoubleCoset
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SnFam.CvScal

variable {D : D7}

lemma mem_orth_iff' {U : Submodule D.host.E (VS D).V} {y : (VS D).V} :
    y ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x y = 0 := by
  simp [orth, Submodule.mem_iInf]

lemma orth_anti {U U' : Submodule D.host.E (VS D).V} (h : U ≤ U') : orth (VS D) U' ≤ orth (VS D) U := by
  intro y hy
  rw [mem_orth_iff'] at hy ⊢
  exact fun x hx => hy x (h hx)

lemma z_mem_orth {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : F.fl.z ∈ orth (VS D) (Xsp F) := by
  rw [mem_orth_iff']
  intro x hx
  have hx' : x ∈ Submodule.span D.host.E (Set.range F.fl.e) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x h => obtain ⟨a, rfl⟩ := h; exact F.fl.z_orth a
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

lemma Xsp_le_Xplus {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : Xsp F ≤ Xplus F := by
  show F.fl.X ≤ F.fl.X ⊔ _
  exact le_sup_left

lemma Xa_of_ge {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {j : ℕ} (h : D.R.rS ≤ j) :
    Xflag F j = Xsp F := by
  show F.fl.Xa j = F.fl.X
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, lt_of_lt_of_le i.2 h, rfl⟩

lemma nrat_mapsTo {T : D.host.E} {F : LFlag (VS D) D.R.rS T} {n} (hn : n ∈ NRat F) :
    ∀ x ∈ Xsp F, n x ∈ Xsp F := by
  intro x hx
  have h1 := hn.2.1 D.R.rS x (by rw [Xa_of_ge F (Nat.le_succ _)]; exact hx)
  rw [Xa_of_ge F le_rfl] at h1
  simpa using add_mem h1 hx

lemma map_eq_self {U : Submodule D.host.E (VS D).V} [FiniteDimensional D.host.E U]
    (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h : ∀ x ∈ U, f x ∈ U) :
    U.map (f : (VS D).V →ₗ[D.host.E] (VS D).V) = U :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨x, hx, rfl⟩; exact h x hx) (LinearEquiv.finrank_map_eq f U)

lemma fd_Xsp {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : FiniteDimensional D.host.E (Xsp F) :=
  FiniteDimensional.span_of_finite _ (Set.finite_range _)

lemma nrat_map {T : D.host.E} {F : LFlag (VS D) D.R.rS T} {n} (hn : n ∈ NRat F) :
    (Xsp F).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F :=
  haveI := fd_Xsp F
  map_eq_self n (nrat_mapsTo hn)

lemma sgRel_iff {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (y y' : (VS D).V) (al al' : D.host.E) :
    SgRel F F' y y' al al' ↔ y - y' - (al • F.zt + al' • F'.zt) ∈ Xsp F ⊔ Xsp F' := by
  rw [Submodule.mem_sup]
  unfold SgRel
  constructor
  · rintro ⟨x, hx, x', hx', h⟩; exact ⟨x, hx, x', hx', by rw [h]; abel⟩
  · rintro ⟨x, hx, x', hx', h⟩
    refine ⟨x, hx, x', hx', ?_⟩
    have : y - y' = x + x' + (al • F.zt + al' • F'.zt) := by rw [h]; abel
    rw [this]; abel

end GlobalTheory.SnFam.CvScal

namespace GlobalTheory.SnFam.CvScal
variable {D : D7}

theorem pair_scalar (D : D7) {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (VS D) D.R.rS T)
    (F' F'' : LFlag (VS D) D.R.rS T') (_hΛ : Submodule.IsLattice D.host.E Λ) (hF : F.zt = F.fl.z)
    (hF' : F'.zt = F'.fl.z) (hF'' : F''.zt = F''.fl.z) (n) (hn : n ∈ NRat F) (m) (hm : m ∈ NRat F')
    (hfr : ∀ a, frame F'' a = (n * m) (frame F' a)) : IsScalar Λ F F' F'' (n * m) := by
  have hnm : ∀ v, (n * m) v = n (m v) := fun v => rfl
  have he : ∀ a, F''.fl.e a = n (m (F'.fl.e a)) := by
    intro a
    have := hfr (Fin.castSucc a)
    simpa [frame, FlagG.fvec, Fin.snoc_castSucc, hnm] using this
  have hz : F''.fl.z = n (m F'.fl.z) := by
    have := hfr (Fin.last _)
    simpa [frame, FlagG.fvec, Fin.snoc_last, hnm] using this

  have hX'' : Xsp F'' = (Xsp F').map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    have h1 : Xsp F'' = (Xsp F').map ((n : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (m : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
      show Submodule.span _ _ = Submodule.map _ (Submodule.span _ _)
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext a
      exact he a
    rw [h1, Submodule.map_comp, nrat_map hm]
  have hsup : (Xsp F ⊔ Xsp F').map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F ⊔ Xsp F'' := by
    rw [Submodule.map_sup, nrat_map hn, hX'']
  have nX' : ∀ v ∈ Xsp F', n v ∈ Xsp F'' := fun v hv => hX'' ▸ Submodule.mem_map_of_mem hv
  intro y1 hy1 y2 _ y1' hy1' y2'' _ h12 h12' al al'
  rw [sgRel_iff, sgRel_iff, hF, hF', hF'']
  have oy1 : y1 ∈ orth (VS D) (Xsp F) := orth_anti (Xsp_le_Xplus F) hy1.2
  have oy1' : y1' ∈ orth (VS D) (Xsp F') := orth_anti (Xsp_le_Xplus F') hy1'.2
  have A : y2 - n y1 ∈ Xsp F := by
    have := add_mem h12 (hn.2.2 y1 oy1)
    rw [← neg_mem_iff]; convert this using 1; abel
  have B : y2'' - n y1' ∈ Xsp F'' := by
    have := add_mem h12' (nX' _ (hm.2.2 y1' oy1'))
    convert this using 1; rw [hnm, map_sub]; abel
  have C : F.fl.z - n F.fl.z ∈ Xsp F := by
    have := hn.2.2 _ (z_mem_orth F)
    rw [← neg_mem_iff]; convert this using 1; abel
  have Dd : F''.fl.z - n F'.fl.z ∈ Xsp F'' := by
    have := nX' _ (hm.2.2 _ (z_mem_orth F'))
    convert this using 1; rw [hz, map_sub]
  set d1 := y1 - y1' - (al • F.fl.z + al' • F'.fl.z) with hd1
  set d2 := y2 - y2'' - (al • F.fl.z + al' • F''.fl.z) with hd2
  have key : d2 = n d1 + ((y2 - n y1) - (y2'' - n y1') - al • (F.fl.z - n F.fl.z) - al' • (F''.fl.z - n F'.fl.z)) := by
    simp only [hd1, hd2, map_sub, map_add, map_smul, smul_sub]; abel
  have kmem : (y2 - n y1) - (y2'' - n y1') - al • (F.fl.z - n F.fl.z) - al' • (F''.fl.z - n F'.fl.z) ∈ Xsp F ⊔ Xsp F'' :=
    sub_mem (sub_mem (sub_mem (Submodule.mem_sup_left A) (Submodule.mem_sup_right B))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left C))) (Submodule.smul_mem _ _ (Submodule.mem_sup_right Dd))
  rw [key, Submodule.add_mem_iff_left _ kmem, ← hsup]
  constructor
  · intro h; exact Submodule.mem_map_of_mem h
  · rintro ⟨w, hw, hw'⟩
    have : w = d1 := n.injective hw'
    exact this ▸ hw

end GlobalTheory.SnFam.CvScal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PartsOfLat
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.Parts
open GlobalTheory.RowsOrb.Uniq

variable {D : D7} (X : HidaSetting D)

theorem lsS_le {r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (v : Fin r → (VS D).V) {y : (VS D).V} (hy : y ∈ latSpanS aa v) :
    y ∈ Submodule.span D.host.E (Set.range v) := by
  have hle : latSpanS aa v ≤ (Submodule.span D.host.E (Set.range v)).restrictScalars (𝓞 D.host.E) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, x, -, rfl⟩
    exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)
  exact hle hy

theorem Xsp_eq (u : D.what₂.Word) : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range X.eX) := by
  show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
  rw [X.Fu_e]

theorem XS_eq (u : D.what₂.Word) : XS D (X.Fu u) = latSpanS (fun a => aaD D a) X.eX := by
  simp only [XS, latSpanS, aaD, X.Fu_e]

theorem xlam_split (u : D.what₂.Word) (M : Submodule (𝓞 D.host.E) (VS D).V)
    (hM : ∀ x ∈ M, ∀ a, (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0) :
    XLam (latSpanS (fun a => aaD D a) X.eX ⊔ M ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) =
      XS D (X.Fu u) := by
  rw [XS_eq]
  show _ ⊓ toO (VS D) (Xsp (lf D (X.Fu u))) = _
  rw [Xsp_eq]
  refine le_antisymm ?_ (le_inf (le_sup_left.trans le_sup_left) fun y hy => lsS_le _ _ hy)
  rintro y ⟨hyΛ, hyX⟩
  have hyX' : y ∈ Submodule.span D.host.E (Set.range X.eX) := hyX
  obtain ⟨y1, hy1, b, hb, rfl⟩ := Submodule.mem_sup.mp hyΛ
  obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.mp hy1
  have haX := lsS_le _ _ ha
  have hbY := lsS_le _ _ hb

  have hb0 : b = 0 := by
    have hpair : ∀ c, (VS D).hT (X.eX c) b = 0 := by
      intro c
      have h1 := orth_span (fun d => X.ee c d) hyX'
      have h2 := orth_span (fun d => X.ee c d) haX
      rw [map_add, map_add, h2, (hM m hm c).1, zero_add, zero_add] at h1
      exact h1
    rw [coord X.ef hbY]
    simp [hpair]
  subst hb0
  rw [add_zero] at hyX' ⊢

  have hmX : m ∈ Submodule.span D.host.E (Set.range X.eX) := by
    have := Submodule.sub_mem _ hyX' haX
    rwa [add_sub_cancel_left] at this
  have hm0 : m = 0 := by
    rw [coord (dual_symm GlobalTheory.RowsOrb.Uniq.hh X.ef) hmX]
    simp [(hM m hm _).2]
  rw [hm0, add_zero]
  exact ha

theorem map_perp (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)) :
    ∀ x ∈ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)), ∀ a,
      (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0 := by
  intro x hx a
  obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hx
  exact (GlobalTheory.RowsOrb.mem_Wb X (w : (VS D).V)).mp w.2 a

theorem lmap_eq (u : D.what₂.Word) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)) :
    GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔
      L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
      latSpanS (fun a => (aaD D a)⁻¹) X.fY) = L := by
  ext w
  rw [lmap_char X u (latSpanS (fun a => aaD D a) X.eX ⊔
      L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
      latSpanS (fun a => (aaD D a)⁻¹) X.fY) (fun a => aaD D a) (fun a => (aaD D a)⁻¹) X.ef (map_perp X L)
      rfl w]
  constructor
  · rintro ⟨l, hl, hP⟩
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hl
    have hfix : P (VS D).hT X.eX X.fY (w' : (VS D).V) = w' := by
      rw [P_apply]
      simp [((GlobalTheory.RowsOrb.mem_Wb X (w' : (VS D).V)).mp w'.2 _).2]
    have : w' = w := Subtype.ext (hfix.symm.trans hP)
    exact this ▸ hw'
  · intro hw
    refine ⟨(w : (VS D).V), Submodule.mem_map_of_mem hw, ?_⟩
    rw [P_apply]
    simp [((GlobalTheory.RowsOrb.mem_Wb X (w : (VS D).V)).mp w.2 _).2]

end GlobalTheory.RowsOrb.Parts

open GlobalTheory.RowsOrb.Parts in

theorem GlobalTheory.RowsOrb.parts_of_lat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), XLam (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) = XS D (X.Fu u) ∧ XLam (VS D).L0 (lf D (X.Fu u)) = XS D (X.Fu u) ∧ GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) = L ∧ ∀ w : GlobalTheory.RowsOrb.Wb X, (w : (VS D).V) ∈ Lsub (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) → w ∈ L := by
  intro D X u L
  refine ⟨xlam_split X u _ (map_perp X L), ?_, lmap_eq X u L, ?_⟩
  · rw [X.Lam_split]
    exact xlam_split X u X.Lb X.Lb_perp
  · intro w hw
    rw [Lsub, Submodule.mem_inf] at hw
    have hX : toO (VS D) (Xsp (lf D (X.Fu u))) =
        GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := by
      rw [GlobalTheory.RowsOrb.Uniq.fixedFrameOfWord_isotropicSpan_eq, Xsp_eq]
    have hmem : w ∈ GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔
        L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
        latSpanS (fun a => (aaD D a)⁻¹) X.fY) :=
      (GlobalTheory.RowsOrb.mem_Lmap X u _ w).mpr ((sup_le_sup inf_le_left hX.le) hw.1)
    rwa [lmap_eq X u L] at hmem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeVolumeUnitaryGroupEq
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

namespace GlobalTheory.UnitaryVolume

theorem Jm_allPos (N : ℕ) : Formalism.REAL.Jm (allPos N) = 1 := by
  simp [Formalism.REAL.Jm, allPos]

theorem mul_conjTranspose_self {N : ℕ} (g : Formalism.REAL.UJ (allPos N)) : uMat g * (uMat g)ᴴ = 1 := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm (allPos N) * uMat g = Formalism.REAL.Jm (allPos N) := g.2
  rw [Jm_allPos, Matrix.mul_one] at h
  exact mul_eq_one_comm.1 h

theorem row_norm {N : ℕ} (g : Formalism.REAL.UJ (allPos N)) (i : Fin N) : ∑ k, ‖uMat g i k‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (mul_conjTranspose_self g) i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ k, ‖uMat g i k‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (Complex.mul_conj' _).symm
  exact_mod_cast h2

theorem muG_univ_lt_top (N : ℕ) : Formalism.REAL.muG (allPos N) Set.univ < ⊤ := by
  have h := Formalism.REAL.ballFinite N (allPos N) N
  have e : {g : Formalism.REAL.UJ (allPos N) | Formalism.REAL.hsG g ≤ (N : ℝ)} = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    change ∑ i, ∑ k, ‖uMat g i k‖ ^ 2 ≤ (N : ℝ)
    simp [row_norm]
  rwa [e] at h

theorem muG_univ_ne_zero (N : ℕ) : Formalism.REAL.muG (allPos N) Set.univ ≠ 0 :=
  (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'

theorem gauss_inv_single {n : ℕ} (g : Formalism.REAL.UJ (allPos (n + 1))) :
    gauss ((uMat g)⁻¹ *ᵥ (Pi.single 0 1 : Fin (n + 1) → ℂ)) = Real.exp (-1) := by
  rw [Matrix.inv_eq_right_inv (mul_conjTranspose_self g), gauss]
  congr 2
  rw [← row_norm g 0]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mulVec_single_one, Matrix.conjTranspose_apply]

theorem volU_succ (n : ℕ) :
    volU (n + 1) = volU n * (2 ^ (n + 1) * Real.pi ^ (n + 1) / (n.factorial : ℝ)) := by
  have h : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
    rw [← Nat.choose_two_right, ← Nat.choose_two_right, Nat.choose_succ_succ' n 1]
    simp [add_comm]
  unfold volU sphV
  rw [Finset.prod_Icc_succ_top (by omega), h]
  simp only [Nat.add_sub_cancel]
  ring

theorem volU_pos (n : ℕ) : 0 < volU n := by
  unfold volU sphV
  have := Real.pi_pos
  exact mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

theorem volume_zero (c : ℝ) (hc : IsGauge (allPos 0) c) :
    c * (Formalism.REAL.muG (allPos 0) Set.univ).toReal = volU 0 := by
  have h1 : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (0 ^ 2))) 1)).toReal = 1 := by
    change (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)).toReal = 1
    have e : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1 = Set.univ :=
      Set.eq_univ_of_forall fun x => by rw [Subsingleton.elim x 0]; simp
    rw [e, ← (PiLp.volume_preserving_toLp (Fin 0)).measure_preimage MeasurableSet.univ.nullMeasurableSet]
    simp [volume_pi, Measure.pi_univ]
  unfold IsGauge at hc
  rw [h1] at hc
  have h2 : Filter.Tendsto (fun _ : ℝ => c * (Formalism.REAL.muG (allPos 0) Set.univ).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have e : {g : Formalism.REAL.UJ (allPos 0) | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} = Set.univ :=
      Set.eq_univ_of_forall fun g => by
        simpa [Formalism.REAL.hs] using le_of_lt hr
    rw [e]
    simp
  rw [tendsto_const_nhds_iff.1 h2]
  simp [volU, sphV]

theorem volume_unitary : ∀ (N : ℕ) (c : ℝ), IsGauge (allPos N) c →
    c * (Formalism.REAL.muG (allPos N) Set.univ).toReal = volU N := by
  intro N
  induction N with
  | zero => exact volume_zero
  | succ n ih =>
    intro c hc
    obtain ⟨c₀, hc₀, -, hu⟩ := GlobalTheory.GaugeConst.gauge_exists_pos_unique (n + 1) (allPos (n + 1))
    have hcpos : 0 < c := by rw [hu c hc]; exact hc₀
    obtain ⟨c', hc'pos, hc', -⟩ := GlobalTheory.GaugeConst.gauge_exists_pos_unique n (allPos n)
    have hv := ih c' hc'
    let x₀ : Fin (n + 1) → ℂ := Pi.single 0 1
    let B : Matrix (Fin (n + 1)) (Fin n) ℂ := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix id Fin.succ
    have hq : qEps (allPos (n + 1)) x₀ = sgn ℝ true := by
      simp [qEps, sgn, allPos, x₀, Fin.sum_univ_succ]
    have hx : star x₀ ᵥ* (Formalism.REAL.Jm (allPos (n + 1)) * B) = 0 := by
      rw [Jm_allPos, Matrix.one_mul]
      funext k
      simp [Matrix.vecMul, dotProduct, x₀, B, Fin.sum_univ_succ, Matrix.one_apply, (Fin.succ_ne_zero k).symm]
    have hB : Bᴴ * Formalism.REAL.Jm (allPos (n + 1)) * B = Formalism.REAL.Jm (allPos n) := by
      rw [Jm_allPos, Jm_allPos, Matrix.mul_one]
      ext a b
      simp [Matrix.mul_apply, B, Matrix.one_apply, eq_comm]
    obtain ⟨j, -, hj⟩ := GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal (n + 1) n _ _ true x₀ B rfl
      hq hx hB
    have hV : ENNReal.ofReal c' * Formalism.REAL.muG (allPos n) Set.univ = ENNReal.ofReal (volU n) := by
      rw [← hv, ENNReal.ofReal_mul hc'pos.le, ENNReal.ofReal_toReal (muG_univ_lt_top n).ne]
    have key := GlobalTheory.T.gauge_measure_quotient_unitaryJ_vector_stabiliser n _ _ true x₀ B j hq hx hB hj c c' hc hc'
      (fun _ => ENNReal.ofReal (volU n)⁻¹) measurable_const (fun g => by
        rw [lintegral_const, mul_left_comm, hV, ← ENNReal.ofReal_mul (inv_pos.2 (volU_pos n)).le,
          inv_mul_cancel₀ (volU_pos n).ne', ENNReal.ofReal_one])
    have hs : sgn ℝ true = 1 := by simp [sgn]
    simp only [x₀, gauss_inv_single, lintegral_const] at key
    rw [hs, GlobalTheory.GaussMean.Sphere.gaussDens_sphere] at key
    have k2 := congrArg ENNReal.toReal key
    have hp := volU_pos n
    have hπ := Real.pi_pos
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos.le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofReal (inv_pos.2 hp).le,
      ENNReal.toReal_ofReal (by positivity)] at k2
    rw [volU_succ]
    have he := Real.exp_pos (-1)
    have hf : (0 : ℝ) < n.factorial := by positivity
    field_simp at k2 ⊢
    linarith

end GlobalTheory.UnitaryVolume
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsEqOfStabilizerConjugateLatticesStatement
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_eq_of_stabilizer_conjugate_lattices : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ Λ₁ ∈ Y.what₂ u, ∀ Λ₂ ∈ Y.what₂ u, ∀ g : GlobalTheory.RowsOrb.Gz X u, g • GlobalTheory.RowsOrb.Lmap X u Λ₁ = GlobalTheory.RowsOrb.Lmap X u Λ₂ → Λ₁ = Λ₂ := by
  first | exact @GlobalTheory.RowsOrb.rows_eq_of_conj | exact GlobalTheory.RowsOrb.rows_eq_of_conj | (intros; apply GlobalTheory.RowsOrb.rows_eq_of_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPointsStatement
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints : ∀ (I : AutInst), SecondCountableTopology I.Gf := by
  first | exact @GlobalTheory.CongTop.secondCountable_finiteAdelicPoints | exact GlobalTheory.CongTop.secondCountable_finiteAdelicPoints | (intros; apply GlobalTheory.CongTop.secondCountable_finiteAdelicPoints <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardLatticeDualVectorsChangeUnipotentStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardLattice_dualVectors_change_unipotent : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0) (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0) (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0), Fr.T ≠ 0 → ∀ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L → ∃ m ∈ Fr.N, (∀ b, m (Fr.f b) = Fr.f b) ∧ (⟨Fr.f, es₂, Fr.T, Fr.h_iso, Fr.h_zz, h1, h2, h3⟩ : LocNG.FrameD H r).LamStd L = LocNG.img m (Fr.LamStd L) := by
  first | exact @GlobalTheory.SwapStd.lamStd_swap | exact GlobalTheory.SwapStd.lamStd_swap | (intros; apply GlobalTheory.SwapStd.lamStd_swap <;> assumption)
end

