import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

-- bundled from Formalism.LocalRingCardinality.DataKerP
section
open Formalism.MainNotions.G NumberField

noncomputable section

namespace Formalism.BasicNotions

structure TwForms (D : D7) where
  A : ∀ u μ, ColumnsAtT D.R (D.chTw u μ)
  A_T : ∀ u μ, (A u μ).T = (D.mem u).A.T
  fm : ∀ u μ, MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) (D.chTw u μ) (A u μ) (D.PTw u μ)

  e0 : ∀ u μ, ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] ((fm u μ).lat 0).V
  twist_preserves_base_lattice : ∀ u μ (x : ((D.fm u).lat 0).V), x ∈ ((D.fm u).lat 0).L ↔ e0 u μ x ∈ ((fm u μ).lat 0).L
  embed_mul_block_embedding : ∀ u μ (x : ((D.fm u).lat 0).V), (fm u μ).emb 0 (e0 u μ x) = D.e0Tw u μ ((D.fm u).emb 0 x)

  eMu0 : ∀ u j, j ≤ D.R.m → (((D.fm u).lat j).V ≃ₗ[D.what₂.LL] ((fm u D.what₂.mu0).lat j).V)
  eMu0_lat : ∀ u j (hj : j ≤ D.R.m) (x : ((D.fm u).lat j).V),
    x ∈ ((D.fm u).lat j).L ↔ eMu0 u j hj x ∈ ((fm u D.what₂.mu0).lat j).L
  eMu0_emb : ∀ u j (hj : j ≤ D.R.m) (x : ((D.fm u).lat j).V),
    HEq ((fm u D.what₂.mu0).emb j (eMu0 u j hj x)) ((D.fm u).emb j x)

structure LocalToGlobal₂ (D : D7) (Gt : GatTies D) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    [Fact (D.what₂.places.resChar w).Prime]
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    (Ch : Chain Lv) where

  fl_t : Fl.t = D.R.t
  fl_m : Fl.mm = D.R.m

  lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]

  iK : (D.gat u w h).Kf →+* ℂ_[D.what₂.places.resChar w]
  iLL_lam : ∀ (x : D.what₂.LL) (hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ),
    iK (c.embW u w h x) = lam ⟨D.what₂.embLL x, hx⟩

  iw : ∀ j (v : Fin (Fl.Pj j).nV), D.host.E →+* (Fl.Pj j).Qq v

  glob : ∀ j, Lv.comp j → (Fl.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((Fl.Pj j).m + 1) → D.host.E)

  glob_loc : ∀ j, j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L → ∀ v,
    L v = Submodule.span ((Fl.Pj j).W v) {y | ∃ x ∈ glob j a L, y = fun i => iw j v (x i)}

  cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u (D.what₂.muAt w)).cls j

  cls_iff : ∀ j, j ≤ D.R.m → ∀ (a a' : Lv.comp j) (L L' : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    (Fl.Pj j).IsLatTup L' →
    (cls j a L = cls j a' L' ↔ a = a' ∧ ∃ γ : (Lv.lev j a).Γ, L' = (Lv.lev j a).smul γ L)
  cls_surj : ∀ j, j ≤ D.R.m → ∀ x : (D.chTw u (D.what₂.muAt w)).cls j, ∃ a L, (Fl.Pj j).IsLatTup L ∧ cls j a L = x

  Th : ∀ j, Lv.comp j × (Fl.Pj j).Tup → Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup →
    MvPowerSeries (D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w]

  cmp : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j
  cmp_inj : ∀ j, j ≤ D.R.m → Function.Injective (cmp j)

  cmp_zero : ∀ x : ((D.fm u).lat 0).V, cmp 0 (Tw.e0 u (D.what₂.muAt w) x) = c.cmp u w h x

  cmp_int : Submodule.span (D.gat u w h).O
    (cmp 0 '' (((Tw.fm u (D.what₂.muAt w)).lat 0).L : Set ((Tw.fm u (D.what₂.muAt w)).lat 0).V)) = Lv.Int 0

  cmp_K : ∀ j, j < D.R.m → ∀ (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) (y : ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V),
    (Tw.fm u (D.what₂.muAt w)).emb (j + 1) y = (D.chTw u (D.what₂.muAt w)).K j ((Tw.fm u (D.what₂.muAt w)).emb j x) →
    cmp (j + 1) y = Ch.Kz j (cmp j x)

def LocalToGlobal₂.CmpIntAll {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word}
    {w : D.what₂.places.Pl} [Fact (D.what₂.places.resChar w).Prime]
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    {Ch : Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) : Prop :=
  ∀ j, j ≤ D.R.m → Submodule.span (D.gat u w h).O
    (Kp.cmp j '' (((Tw.fm u (D.what₂.muAt w)).lat j).L : Set ((Tw.fm u (D.what₂.muAt w)).lat j).V)) = Lv.Int j

theorem LocalToGlobal₂.cmp_KL {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word}
    {w : D.what₂.places.Pl} [Fact (D.what₂.places.resChar w).Prime]
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    {Ch : Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) (j : ℕ) (hj : j < D.R.m)
    (hK : (Tw.fm u (D.what₂.muAt w)).KRat j) (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) :
    Kp.cmp (j + 1) ((Tw.fm u (D.what₂.muAt w)).KL j hK x) = Ch.Kz j (Kp.cmp j x) :=
  Kp.cmp_K j hj x _ ((Tw.fm u (D.what₂.muAt w)).KL_spec j hK x)

end Formalism.BasicNotions
end
end

-- bundled from Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
section
namespace Formalism.BasicNotions

theorem D7.eight_le_f (D : D7) : 8 ≤ D.R.f := by
  have h : 2 ≤ D.R.e := D.host.two_le_e
  have h4 : 2 ^ 2 ≤ 2 ^ D.R.e := Nat.pow_le_pow_right (by norm_num) h
  have h5 : 2 ^ D.R.e ≤ D.R.ord := D.R.toFrame.two_pow_le_ord
  unfold Ranks.f Ranks.n
  omega

theorem ParamsT.t_ge_fourth_power_rank {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    128 * D.R.r ^ 4 ≤ D.R.t := by
  have hf := D.eight_le_f
  have h1 : D.R.f * D.R.r * (D.R.r + 1) ≤ T.nWn := T.nW_lo.1
  have h2 : 8 * D.R.r ^ 2 ≤ T.nWn := by
    refine le_trans ?_ h1
    calc 8 * D.R.r ^ 2 = 8 * D.R.r * D.R.r := by ring
      _ ≤ D.R.f * D.R.r * (D.R.r + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hf) (Nat.le_succ _)
  have h3 : 2 * T.nWn ≤ T.TO := by
    have := T.TO_nW
    have h' : 2 * T.nWn ≤ (T.Dp + 2) * T.nWn := Nat.mul_le_mul_right _ (by omega)
    omega
  have h4 : 128 * D.R.r ^ 4 ≤ T.TO * T.nWn := by
    calc 128 * D.R.r ^ 4 = (2 * (8 * D.R.r ^ 2)) * (8 * D.R.r ^ 2) := by ring
      _ ≤ (2 * T.nWn) * T.nWn := Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h2
      _ ≤ T.TO * T.nWn := Nat.mul_le_mul_right _ h3
  have h5 : D.R.r ≤ T.nP := by
    rw [T.nP_eq]
    have : D.R.r ≤ 8 * D.R.f * D.R.r := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h6 := T.split
  omega

theorem ParamsT.t_ge_80 {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    80 * (D.R.r : ℝ) ^ ((7 : ℝ) / 2) ≤ (D.R.t : ℝ) := by
  have h : ((128 * D.R.r ^ 4 : ℕ) : ℝ) ≤ (D.R.t : ℝ) := by exact_mod_cast T.t_ge_fourth_power_rank
  push_cast at h
  rcases Nat.eq_zero_or_pos D.R.r with h0 | h0
  · rw [h0]; simp
  · have h1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast h0
    have h2 : (D.R.r : ℝ) ^ ((7 : ℝ) / 2) ≤ (D.R.r : ℝ) ^ ((4 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    rw [Real.rpow_natCast] at h2
    have h3 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 4 := by positivity
    linarith

theorem ParamsT.two_rank_sq_lt_t {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (hr : 0 < D.R.r) :
    2 * D.R.r ^ 2 + 2 < D.R.t := by
  have h := T.t_ge_fourth_power_rank
  have h1 : D.R.r ^ 2 ≤ D.R.r ^ 4 := Nat.pow_le_pow_right hr (by norm_num)
  have h2 : 1 ≤ D.R.r ^ 2 := Nat.one_le_pow _ _ hr
  omega

theorem ParameterChoice'.m_sq_le_k {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : D.R.m ^ 2 ≤ D.R.k := by
  have h1 : (1 : ℝ) ≤ L.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have h2 := P.k_ge_m2L
  have h3 : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by positivity
  have h4 : (D.R.m : ℝ) ^ 2 ≤ (D.R.k : ℝ) := by nlinarith
  exact_mod_cast h4

theorem ParameterChoice'.three_q_le {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (j : ℕ) (hj : 1 ≤ j) :
    3 * (D.R.sigW j).2 + 1 ≤ D.R.r := by
  have h := P.m_sq_le_k
  have h2 := D.R.two_le_m
  have h3 : 2 * D.R.m ≤ D.R.m ^ 2 := by
    calc 2 * D.R.m ≤ D.R.m * D.R.m := Nat.mul_le_mul_right _ h2
      _ = D.R.m ^ 2 := by ring
  unfold Ranks.sigW Ranks.r
  simp only
  omega

def D7.NodeGap (D : D7) (h : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m),
    h ≤ (((D.hcW u τ).b ⟨j + 1, hj⟩ - (D.hcW u τ).b ⟨j, by omega⟩ : ℚ) : ℝ)

theorem D7.NodeGap.mono {D : D7} {h h' : ℝ} (H : D.NodeGap h) (hle : h' ≤ h) : D.NodeGap h' :=
  fun u τ j hj => le_trans hle (H u τ j hj)

theorem ParameterChoice'.nodeGap_ge_heightBound {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : D.NodeGap (LevelStarExponents.h0 L) := by
  intro u τ j hj
  rw [D.hcW_b u τ]
  exact (P.nodes_gap τ j hj).1

theorem ParameterChoice'.nodeGap_ge_cubic_rank {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) :
    D.NodeGap (4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6) :=
  P.nodeGap_ge_heightBound.mono P.h0_ge.2.2.2.2.1

theorem ParamsT.heightBound_ge_fourth_power_rank {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    256 * (D.R.r : ℝ) ^ 4 ≤ LevelStarExponents.h0 L := by
  have h1 : ((128 * D.R.r ^ 4 : ℕ) : ℝ) ≤ (D.R.t : ℝ) := by exact_mod_cast T.t_ge_fourth_power_rank
  push_cast at h1
  have h2 := P.h0_ge.2.2.2.2.1
  have h3 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
  linarith

theorem ParamsT.nodeGap_ge_fourth_power_rank {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    D.NodeGap (256 * (D.R.r : ℝ) ^ 4) :=
  P.nodeGap_ge_heightBound.mono T.heightBound_ge_fourth_power_rank

end Formalism.BasicNotions
end

-- bundled from Formalism.LocalRingCardinality.PosOfIsomEmb
section
noncomputable section

namespace Formalism.BasicNotions

open NumberField

section gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem HSpace.pos_of_isomEmb (A B : HSpace E) (ι : A.V →ₗ[E] B.V) (hι : HSpace.IsIsomEmb A B ι)
    (hA : A.SigOK) (hB : B.SigOK) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hdef : A.sig τ = (A.rank, 0) ∨ A.sig τ = (0, A.rank)) (hlt : (B.sig τ).2 < A.rank) :
    A.sig τ = (A.rank, 0) := by
  rcases hdef with h | h
  · exact h
  · exfalso
    have hw : (Matrix.of fun i j => B.hT (ι (A.frame i)) (ι (A.frame j))) = A.gram := by
      ext i j; exact hι _ _
    have hsA := hA τ
    rw [h, ← hw] at hsA
    have key := (sig_family B τ hτ _ hsA (hB τ)).2
    have hs := sig_sum B hB τ
    simp only at key
    omega

theorem HSpace.frame_of_pos (S : HSpace E) (σ : E →+* ℂ)
    (hσ : ∀ a, σ (star a) = (starRingEnd ℂ) (σ a)) (h : Formalism.UG.HasSignature (S.gram.map σ) S.rank 0) :
    ∃ Y : Matrix (Fin S.rank) (Fin S.rank) ℂ, IsUnit Y.det ∧
      ∀ y : S.V, ∑ i, ‖(Y.mulVec fun j => σ (S.frame.repr y j)) i‖ ^ 2 = (σ (S.hT y y)).re := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq S.rank 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  set Pm : Matrix (Fin S.rank ⊕ Fin 0) (Fin S.rank ⊕ Fin 0) ℂ := P.val with hPm
  set Qm : Matrix (Fin S.rank ⊕ Fin 0) (Fin S.rank ⊕ Fin 0) ℂ := (P⁻¹).val with hQm
  have hPQ : Pm * Qm = 1 := by rw [hPm, hQm, ← Units.val_mul, mul_inv_cancel]; rfl
  have hcT : Formalism.UG.cT (starRingEnd ℂ) Pm = Pm.conjTranspose := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  set G : Matrix (Fin S.rank) (Fin S.rank) ℂ := S.gram.map σ with hG
  have hGr : G.reindex e e = Qm.conjTranspose * Qm := by
    have h1 : Qm.conjTranspose * (Pm.conjTranspose * G.reindex e e * Pm) * Qm = Qm.conjTranspose * Qm := by
      rw [hP, Matrix.mul_one]
    have h2 : Qm.conjTranspose * Pm.conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
    rw [← h1]
    calc G.reindex e e = (Qm.conjTranspose * Pm.conjTranspose) * G.reindex e e * (Pm * Qm) := by
          rw [h2, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  let Y : Matrix (Fin S.rank) (Fin S.rank) ℂ := Qm.submatrix e e
  have hGY : G = Y.conjTranspose * Y := by
    have : G = (G.reindex e e).submatrix e e := by ext i j; simp
    rw [this, hGr]
    ext i j
    simp only [Y, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact (Equiv.sum_comp e _).symm
  refine ⟨Y, ?_, fun y => ?_⟩
  · have : Y.det = Qm.det := Matrix.det_submatrix_equiv_self e Qm
    rw [this]
    exact (Matrix.isUnit_iff_isUnit_det _).mp ⟨P⁻¹, rfl⟩
  · set z : Fin S.rank → ℂ := fun j => σ (S.frame.repr y j) with hz
    have h1 : ∑ i, ‖(Y.mulVec z) i‖ ^ 2 = (star (Y.mulVec z) ⬝ᵥ Y.mulVec z).re := by
      simp [dotProduct, Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
    have h2 : star (Y.mulVec z) ⬝ᵥ Y.mulVec z = star z ⬝ᵥ G.mulVec z := by
      rw [hGY, Matrix.star_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star z)]
    have h3 : σ (S.hT y y) = star z ⬝ᵥ G.mulVec z := by
      have := LinearMap.sum_repr_mul_repr_mulₛₗ S.frame S.frame (B := S.hT) y y
      rw [← this, Finsupp.sum_fintype _ _ (by intro i; simp)]
      simp only [dotProduct, Matrix.mulVec, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_fintype _ _ (by intro j; simp), map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [smul_eq_mul, map_mul, RingHom.id_apply, hG, hz, Matrix.map_apply, HSpace.gram, Pi.star_apply]
      rw [starRingEnd_apply, hσ]
      simp only [starRingEnd_apply]
      ring
    rw [h1, h2, h3]

theorem HSpace.form_pos (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = (starRingEnd ℂ) (τ a)) (h : S.sig τ = (S.rank, 0)) (x : S.V) (hx : x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ τ (S.hT x x) = (c : ℂ) := by
  have hsig := hS τ
  rw [h] at hsig
  obtain ⟨Y, hY, hsum⟩ := S.frame_of_pos τ hτ hsig
  have hz : (fun j => τ (S.frame.repr x j)) ≠ 0 := by
    intro h0
    apply hx
    apply S.frame.repr.injective
    ext j
    have := congrFun h0 j
    simpa using this
  have hYz : Y.mulVec (fun j => τ (S.frame.repr x j)) ≠ 0 := by
    intro h0
    apply hz
    have hinj : Function.Injective Y.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det Y).mpr hY)
    exact hinj (by rw [h0, Matrix.mulVec_zero])
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hYz
  have hpos : 0 < (τ (S.hT x x)).re := by
    rw [← hsum x]
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, ?_⟩
    have : 0 < ‖(Y.mulVec fun j => τ (S.frame.repr x j)) i‖ := norm_pos_iff.mpr hi
    positivity
  have hre : τ (S.hT x x) = starRingEnd ℂ (τ (S.hT x x)) := by
    rw [← hτ]
    congr 1
    exact ((S.herm.eq x x)).symm
  refine ⟨(τ (S.hT x x)).re, hpos, ?_⟩
  apply Complex.ext
  · simp
  · have := congrArg Complex.im hre
    simp only [Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

end gen

section spaces

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E]

theorem Spaces.X'_posDef (S : Spaces R F E) (hYm : ∀ τ : E →+* ℂ, (S.Y R.m).sig τ = sigYD R R.m) :
    S.X'.IsPosDef := by
  intro τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := S.cm.cmUnram.2.1 τ
  refine HSpace.pos_of_isomEmb S.X' (S.Y R.m) S.eYm.toLinearMap S.eYm_isom S.X'_sig (S.Y_sig R.m) τ hτ
    ((factXmDef R F S).1 τ) ?_
  rw [hYm τ, S.X'_rank]
  simp only [sigYD, Nat.sub_self, Nat.zero_div]
  unfold Ranks.rankX' Ranks.r
  have := R.k_ge
  omega

theorem Spaces.X_posDef (S : Spaces R F E)
    (hY : ∀ j, j ≤ R.m → ∀ τ : E →+* ℂ, (S.Y j).sig τ = sigYD R j) (j : ℕ) (hj : j ≤ R.m) :
    (S.X j).IsPosDef := by
  intro τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := S.cm.cmUnram.2.1 τ
  rcases Nat.lt_or_ge j R.m with hjm | hjm
  · refine HSpace.pos_of_isomEmb (S.X j) (S.Y j) (S.iXY j) (S.iXY_isom j hjm) (S.X_sig j) (S.Y_sig j) τ hτ
      (S.X_def j hj τ) ?_
    rw [hY j hj τ, S.X_rank j hj]
    simp only [sigYD, Ranks.N]
    have h1 := R.m_add_three_le_k
    have h2 : (R.m - j) / 2 < R.k := by omega
    exact lt_of_lt_of_le h2 (Nat.le_add_right _ _)
  · have hjm' : j = R.m := le_antisymm hj hjm
    subst hjm'
    have hX' := Spaces.X'_posDef S (hY R.m le_rfl) τ
    rw [S.X'_rank] at hX'
    rw [S.X_rank R.m le_rfl]
    exact ((factXmDef R F S).2.2 τ).2 hX'

theorem Spaces.X_form_pos (S : Spaces R F E)
    (hY : ∀ j, j ≤ R.m → ∀ τ : E →+* ℂ, (S.Y j).sig τ = sigYD R j) (j : ℕ) (hj : j ≤ R.m)
    (τ : E →+* ℂ) (x : (S.X j).V) (hx : x ≠ 0) : ∃ c : ℝ, 0 < c ∧ τ ((S.X j).hT x x) = (c : ℂ) :=
  HSpace.form_pos (S.X j) (S.X_sig j) τ (S.cm.cmUnram.2.1 τ) (S.X_posDef hY j hj τ) x hx

end spaces

namespace D7

variable (D : D7)

theorem X_posDef (j : ℕ) (hj : j ≤ D.R.m) : letI := D.host.cmStar; (D.sp.X j).IsPosDef :=
  letI := D.host.cmStar; D.sp.X_posDef D.Y_sigval j hj

theorem X'_posDef : letI := D.host.cmStar; D.sp.X'.IsPosDef :=
  letI := D.host.cmStar; D.sp.X'_posDef (D.Y_sigval D.R.m le_rfl)

theorem X_form_pos (j : ℕ) (hj : j ≤ D.R.m) (τ : D.host.E →+* ℂ) :
    letI := D.host.cmStar; ∀ x : (D.sp.X j).V, x ≠ 0 → ∃ c : ℝ, 0 < c ∧ τ ((D.sp.X j).hT x x) = (c : ℂ) :=
  letI := D.host.cmStar; fun x hx => D.sp.X_form_pos D.Y_sigval j hj τ x hx

end D7

end Formalism.BasicNotions

end
end

