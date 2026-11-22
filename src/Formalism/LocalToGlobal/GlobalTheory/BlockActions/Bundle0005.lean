import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle0004
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.InJSymRestrict
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

section Gen

theorem inJSym_restrict {κ : Type} [Field κ] {n : ℕ} {k rS t : ℕ} {zl : Bool} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ)
    (R : Matrix (Fin n) (Fin n) κ) (hR : ∀ x y, R x y = M x.castSucc y.castSucc) (h : InJSym k rS t zl M) :
    InJSym k rS t false R := by
  obtain ⟨h1, h2, h3, -⟩ := h
  refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun h => absurd h Bool.false_ne_true⟩
  · rw [hR]; exact h1 _ _ (by simpa only [Fin.val_castSucc] using hxy)
  · rw [hR]; exact h2 _ (by simpa only [Fin.val_castSucc] using hx)
  · rw [hR]; exact h3 _ _ (by simpa only [Fin.val_castSucc] using hx) (by simpa only [Fin.val_castSucc] using hy)

theorem jsym_of_blk {κ : Type} [Field κ] {n N : ℕ} (hN : n + 1 = N) {k rS t : ℕ} (Mm : GL (Fin N) κ)
    (hMm : Mm ∈ JSymG κ N k rS t true) (R : Matrix (Fin n) (Fin n) κ)
    (hR : ∀ x y : Fin n, R x y = Mm.1 ⟨x, by omega⟩ ⟨y, by omega⟩) :
    ∃ M ∈ JSymG κ n k rS t false, M.1 = R := by
  subst hN
  obtain ⟨h1, h2⟩ := hMm
  have hRc : ∀ x y : Fin n, R x y = Mm.1 x.castSucc y.castSucc := fun x y => hR x y
  set R' : Matrix (Fin n) (Fin n) κ := fun x y => (Mm⁻¹ : GL (Fin (n + 1)) κ).1 x.castSucc y.castSucc with hR'
  have hl : ∀ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ), InJSym k rS t true M → ∀ x : Fin n,
      M x.castSucc (Fin.last n) = 0 := by
    intro M hM x
    have := (hM.2.2.2 rfl x.castSucc (Fin.last n) (by simp)).1
    simpa [Fin.castSucc_ne_last] using this
  have hmul : ∀ (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) κ), InJSym k rS t true A → ∀ x y : Fin n,
      (A * B) x.castSucc y.castSucc = ∑ j : Fin n, A x.castSucc j.castSucc * B j.castSucc y.castSucc := by
    intro A B hA x y
    rw [mul_apply, Fin.sum_univ_castSucc, hl A hA x, zero_mul, add_zero]
  have e1 : R * R' = 1 := by
    ext x y
    have := congrFun (congrFun (Mm.mul_inv) x.castSucc) y.castSucc
    rw [hmul _ _ h1] at this
    rw [mul_apply]
    simp only [hRc, hR']
    rw [this]
    simp [one_apply, Fin.castSucc_inj]
  have e2 : R' * R = 1 := by
    ext x y
    have := congrFun (congrFun (Mm.inv_mul) x.castSucc) y.castSucc
    rw [hmul _ _ h2] at this
    rw [mul_apply]
    simp only [hRc, hR']
    rw [this]
    simp [one_apply, Fin.castSucc_inj]
  refine ⟨⟨R, R', e1, e2⟩, ⟨?_, ?_⟩, rfl⟩
  · exact inJSym_restrict _ R hRc h1
  · exact inJSym_restrict _ R' (fun x y => rfl) h2

theorem blk_conj {K : Type} [CommRing K] {n N : ℕ} (hN : n + 1 = N) (gm Fm Fm' : Matrix (Fin N) (Fin N) K) (hFm : Fm' * Fm = 1)
    (A : Matrix (Fin N) (Fin n) K) (Fp gk M' : Matrix (Fin n) (Fin n) K) (hM' : Fp * M' = gk * Fp)
    (hgA : gm * A = A * gk) (w : Fin N → K) (hgw : gm *ᵥ w = w)
    (hF1 : ∀ x (b : Fin n) (b' : Fin N), (b : ℕ) = b' → Fm x b' = (A * Fp) x b)
    (hF2 : ∀ x (l : Fin N), (l : ℕ) + 1 = N → Fm x l = w x) :
    ∀ x y : Fin n, (Fm' * gm * Fm) ⟨x, by omega⟩ ⟨y, by omega⟩ = M' x y := by
  subst hN
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of (fun x y : Fin (n + 1) =>
    if h : (x : ℕ) < n ∧ (y : ℕ) < n then M' ⟨x, h.1⟩ ⟨y, h.2⟩ else if (x : ℕ) = y then 1 else 0) with hB
  have hne : ∀ j : Fin n, (j : ℕ) ≠ n := fun j => j.is_lt.ne
  have key : gm * Fm = Fm * B := by
    ext x y
    refine Fin.lastCases ?_ (fun y' => ?_) y
    · have e1 : (gm * Fm) x (Fin.last n) = w x := by
        rw [← congrFun hgw x, mul_apply]
        simp only [mulVec, dotProduct]
        exact Finset.sum_congr rfl (fun j _ => by rw [hF2 j (Fin.last n) (by simp)])
      rw [e1, mul_apply, Fin.sum_univ_castSucc]
      simp [hB, hne, hF2 x (Fin.last n) (by simp)]
    · have eL : (gm * Fm) x y'.castSucc = (A * (Fp * M')) x y' := by
        rw [hM', ← Matrix.mul_assoc, ← hgA, Matrix.mul_assoc, mul_apply, mul_apply]
        exact Finset.sum_congr rfl (fun j _ => by rw [hF1 j y' y'.castSucc (by simp)])
      have eR : (Fm * B) x y'.castSucc = ((A * Fp) * M') x y' := by
        rw [mul_apply, Fin.sum_univ_castSucc, mul_apply]
        have hlast : B (Fin.last n) y'.castSucc = 0 := by
          simp [hB, (hne y').symm]
        rw [hlast, mul_zero, add_zero]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hF1 x j j.castSucc (by simp)]
        simp [hB]
      rw [eL, eR, Matrix.mul_assoc]
  intro x y
  have e : Fm' * gm * Fm = B := by rw [Matrix.mul_assoc, key, ← Matrix.mul_assoc, hFm, Matrix.one_mul]
  rw [e]
  simp [hB]

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem redM_entry {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m m' : ℕ}
    (X : Matrix (Fin m) (Fin m) (v.adicCompletion F)) (Y : Matrix (Fin m') (Fin m') (v.adicCompletion F))
    (a b : Fin m) (a' b' : Fin m') (h : X a b = Y a' b') : redM F v X a b = redM F v Y a' b' := by
  simp only [redM, h]
  by_cases hY : Y a' b' ∈ v.adicCompletionIntegers F
  · rw [dif_pos (by rw [h]; exact hY), dif_pos hY]
  · rw [dif_neg (by rw [h]; exact hY), dif_neg hY]

set_option maxHeartbeats 4000000 in

theorem lev_bad (Tf : FormsTiedSym D u Ch chOf) (K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) K.1 G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hlev : bc (prV (E := D.host.E) v) K ∈ levelVL (sigD D) (gramP D) v Tf.clsP.lev.Lb)
    (i : Fin 2) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal) :
    bc (prV (E := D.host.E) v) K ∈ Tf.clsP.lev.Uloc v := by
  set Km := (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev
  rw [Tf.glevP.mem i v h _ hlev]
  have hGv : bc (prV (E := D.host.E) v) G ∈ Km.Uloc v := ((Km.U_eq G).1 hG).2 v
  obtain ⟨Mm, hMm, hMmeq⟩ := (Tf.glevM.mem i v h _ (Km.Uloc_lev v hGv)).1 hGv
  obtain ⟨hEv1, hEv2⟩ := isExt_prV v hE
  obtain ⟨hF1, hF2⟩ := Tf.frExt i v h
  have hmatG : Tf.gl.mat i v h (Tf.glevM.fr i v h) (bc (prV (E := D.host.E) v) G) =
      ((Tf.glevM.fr i v h)⁻¹ : GL _ _).1 * (G.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevM.fr i v h).1 := by
    simp only [GLoc.mat, Units.val_mul]; rfl
  have hmatK : Tf.gl.mat i v h (Tf.glevP.fr i v h) (bc (prV (E := D.host.E) v) K) =
      ((Tf.glevP.fr i v h)⁻¹ : GL _ _).1 * (K.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevP.fr i v h).1 := by
    simp only [GLoc.mat, Units.val_mul]; rfl
  have hb := blk_conj (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R)
    ((G.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h)) (Tf.glevM.fr i v h).1 ((Tf.glevM.fr i v h)⁻¹ : GL _ _).1
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    ((iXm D).map ((Tf.gl.phi i v h).comp (inclE (F := D.host.F) (v.adicCompletion D.host.F))))
    (Tf.glevP.fr i v h).1 ((K.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h))
    (((Tf.glevP.fr i v h)⁻¹ : GL _ _).1 * (K.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevP.fr i v h).1)
    (by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul])
    (by
      have := congrArg (fun M => M.map (Tf.gl.phi i v h)) hEv1
      simp only [Matrix.map_mul, Matrix.map_map] at this
      rw [RingHom.coe_comp]
      exact this)
    (fun a => Tf.gl.phi i v h (inclE (F := D.host.F) (v.adicCompletion D.host.F) (Tf.til.z0 a)))
    (by
      funext a
      exact (RingHom.map_mulVec (Tf.gl.phi i v h) _ _ a).symm.trans (congrArg (fun w => Tf.gl.phi i v h (w a)) hEv2))
    hF1 hF2
  refine jsym_of_blk (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) Mm hMm _ (fun x y => ?_)
  rw [hMmeq]
  refine redM_entry v _ _ _ _ _ _ ?_
  rw [hmatK, hmatG]
  exact (hb x y).symm

set_option maxHeartbeats 4000000 in

theorem lev_mem (Tf : FormsTiedSym D u Ch chOf) (K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) K.1 G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) : K ∈ Tf.clsP.lev.U := by
  have hU : K ∈ UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := lev_unit Tf K.1 G hE hG
  rw [Tf.clsP.lev.U_eq]
  refine ⟨hU, fun v => ?_⟩
  have hu := Formalism.UG.P.base_change_mem_holds _ _ _ (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (sigR (sigD D) (v.adicCompletion D.host.F)) (prV (E := D.host.E) v)
    (Formalism.UG.P.afsplit_prV_comp_sigR (sigD D) v) _ K hU
  have e : ((gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))).map (prV (E := D.host.E) v) =
      (gramP D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) := by
    rw [Matrix.map_map]; rfl
  rw [e] at hu
  have hlev : bc (prV (E := D.host.E) v) K ∈ levelVL (sigD D) (gramP D) v Tf.clsP.lev.Lb :=
    Subgroup.mem_inf.mpr ⟨hu, fun x => lev_lat Tf K.1 G hE hG v x⟩
  by_cases hv : v ∈ badG D
  · obtain ⟨i, hi⟩ : ∃ i : Fin 2, (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal := by
      rcases hv with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
    exact lev_bad Tf K G hE hG v hlev i hi
  · have h1 : ((1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
      rw [Nat.cast_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    rw [Tf.clsP.lev.Uloc_hyp v hv h1]
    exact hlev

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfClassesFrames
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField

theorem exists_map_of_ratSpan (D : D7) {n : ℕ} {lam : D.what₂.Tau → DomWeight n}
    {p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hp : p ∈ RatSpan D lam) :
    ∃ F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL, MvPolynomial.map D.what₂.embLL F = p := by
  have hle : RatSpan D lam ≤ (MvPolynomial.map (σ := D.what₂.Tau × Fin n × Fin n) D.what₂.embLL).range.toAddSubgroup := by
    unfold RatSpan
    refine (AddSubgroup.closure_le _).2 ?_
    rintro q ⟨r, f, -, rfl⟩
    refine RingHom.mem_range.2
      ⟨MvPolynomial.C r * Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_⟩
    have hi : D.what₂.embLL.comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    congr 1
    unfold Formalism.L2.Forms.ten
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.map_rename, MvPolynomial.map_map, hi]
  obtain ⟨F, hF⟩ := RingHom.mem_range.1 (hle hp)
  exact ⟨F, hF⟩

def FramesAt : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (_ : FormsTiedSym D u Ch chOf)
    (s : D.what₂.LL →+* ℂ),
    (∃ o : Frames (gramC (gramN D D.R.m le_rfl) (embS D s)), o.IsON) ∧ ∃ o : Frames (gramC (gramP D) (embS D s)), o.IsON

def NormClsAt : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u →
    ∀ (h : (D.fm u).PRat) (s : D.what₂.LL →+* ℂ) (x : Vl D u D.R.m)
      (Pc : (D.mem u).C.cls D.R.m → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL),
      (∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
        ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z)) →
    ∀ (Qc : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
      (∀ c, Tf.valP.eW ((D.fm u).ptEmb ((D.fm u).PtL h x)) c =
        fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c))) →
    ∀ (o : Frames (gramC (gramN D D.R.m le_rfl) (embS D s))), o.IsON →
    ∀ (o' : Frames (gramC (gramP D) (embS D s))), o'.IsON →
    ∀ c, (∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
        (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re ≤
      ptB D u * ((∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
        (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (subP o.1 (MvPolynomial.map s (Pc ((D.fm u).til c))))
          (subP o.1 (MvPolynomial.map s (Pc ((D.fm u).til c))))).re)

theorem ptB_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ ptB D u :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (zpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)

theorem wt_re_eq (D : D7) (u : D.what₂.Word) (i : ℕ) (c : (D.mem u).C.cls i) :
    ((D.mem u).C.wt i c).re = ((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℝ)⁻¹ := by
  unfold ColumnChain.wt
  rw [show (((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℂ))⁻¹ = ((((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.ofReal_re]

theorem sum_le_of_inj {α β : Type} [Fintype α] [Fintype β] (f : α → β) (hf : Function.Injective f) (a : α → ℝ) (b : β → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, 0 ≤ b y) (hab : ∀ x, a x ≤ B * b (f x)) : ∑ x, a x ≤ B * ∑ y, b y := by
  classical
  calc ∑ x, a x ≤ ∑ x, B * b (f x) := Finset.sum_le_sum fun x _ => hab x
    _ = B * ∑ y ∈ Finset.univ.image f, b y := by
        rw [Finset.sum_image (fun x _ y _ h => hf h), Finset.mul_sum]
    _ ≤ B * ∑ y, b y := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ => hb y) hB

theorem norm_bound_of_classes_frames (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) (hF : FramesAt) (hC : NormClsAt) : NormBoundAtInfinity := by
  intro D u Ch chOf Tf hL hB h v x
  obtain ⟨s, rfl⟩ : ∃ s, InfinitePlace.mk s = v := ⟨v.embedding, v.mk_embedding⟩

  have hx := ((Tf.val D.R.m le_rfl (Or.inr rfl)).rat ((D.fm u).emb D.R.m x)).1 ⟨x, rfl⟩
  choose P hP hPz using hx.2
  choose Pc hPc using fun c => exists_map_of_ratSpan D (hP c)
  have hrep : ∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
      ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z) := fun c z => by rw [hPc c]; exact hPz c z

  have hy := (Tf.valP.rat ((D.fm u).ptEmb ((D.fm u).PtL h x))).1 ⟨_, rfl⟩
  choose Q hQ hQz using hy.2
  choose Qc hQc using fun c => exists_map_of_ratSpan D (hQ c)
  have hrepP : ∀ c, Tf.valP.eW ((D.fm u).ptEmb ((D.fm u).PtL h x)) c =
      fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c)) := fun c => by rw [hQc c]; exact hQz c
  obtain ⟨⟨o, ho⟩, ⟨o', ho'⟩⟩ := hF D u Ch chOf Tf s
  rw [Tf.normP s _ Qc hrepP o' ho', Tf.norm D.R.m le_rfl (Or.inr rfl) s x Pc hrep o ho]
  refine sum_le_of_inj _ (h1 D u Ch chOf Tf) _ _ _ (ptB_nonneg D u) (fun c => ?_) (fun c => ?_)
  · refine mul_nonneg (mul_nonneg ?_ (Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _))
      (Formalism.L2.Ker.ta_nfAll_nonneg ((D.fm u).lam D.R.m) _)
    rw [wt_re_eq]; positivity
  · have hcard : Nat.card ((D.fm u).stabilizer₂ c) = Nat.card ((D.mem u).C.stab D.R.m ((D.fm u).til c)) :=
      Nat.card_congr (Equiv.ofBijective _ (h2 D u Ch chOf Tf c))
    have hk := hC D u Ch chOf Tf hL hB h s x Pc hrep Qc hrepP o ho o' ho' c
    rw [wt_re_eq, ← hcard]
    have hw : 0 ≤ ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ := by positivity
    calc ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re
        = ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * ((∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hk hw
      _ = _ := by ring

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.StabiliserBijectiveOfInjection
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms

theorem bij_of_inj_back {A B : Type} [Finite A] (f : A → B) (hf : Function.Injective f) (g : B → A) (hg : Function.Injective g) :
    Function.Bijective f := by
  haveI : Finite B := Finite.of_injective g hg
  exact hf.bijective_of_nat_card_le (Nat.card_le_card_of_injective g hg)

theorem stabiliser_bijective_of_injection
    (h : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      ∀ c, ∃ g : (D.mem u).C.stab D.R.m ((D.fm u).til c) → (D.fm u).stabilizer₂ c, Function.Injective g) :
    StabiliserMapBijective := by
  intro D u Ch chOf Tf c
  obtain ⟨g, hg⟩ := h D u Ch chOf Tf c
  exact bij_of_inj_back _ ((D.fm u).stabMap_inj c) g hg

end Formalism.L2.GlobalTheoryTheory.Br
end
end

