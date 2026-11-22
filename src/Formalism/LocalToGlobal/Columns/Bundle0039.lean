import Formalism.LocalToGlobal.Columns.TiedMvG
import Formalism.LocalToGlobal.Columns.TiedMvB
import Formalism.LocalToGlobal.Columns.Bundle0033
import Formalism.LocalToGlobal.Columns.Bundle0037
import Formalism.LocalToGlobal.Columns.TwQLev
import Formalism.LocalToGlobal.Columns.Bundle0036
import Formalism.LocalToGlobal.Columns.CoefColLemmas

-- bundled from Formalism.LocalToGlobal.Columns.TiedMvC
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Any

variable {D : ColRec} {u : D.what₂.Word} {A : CF.AtTTied u} {P : ∀ i hi, CF.LvTied u A i hi} (H : CH.HermCols D) (M : AtTMovesC A P)

theorem hxm_adI_up (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (y : ↥(CH.Ld D u i c))
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm).U ((H.cls u i h1 hm).y c)
      ((H.cls u i h1 hm).y ((D.fm u).up i v c ((P i hm).pr v c (hxLd i hm c y))))
      (Formalism.L2.Forms.reGL (CF.rankN D i hm).symm _ (M.upG i hm v c (hxLd i hm c y)).1) (H.vT u v).1) :
    CH.AdI D H u i h1 hm c ((D.fm u).up i v c (hxPr A P i v c y)) (M.toMoves.upG i v c y) v := by
  rw [hxPr_eq A P i hm]
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb (D.sp.X i).frame (M.upS i v c y).1) _
  rw [M.upS_eq i hm, hxG_toGLb]
  exact h

theorem hxm_adI_dn (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c))
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm).U ((H.cls u i h1 hm).y c)
      ((H.cls u i h1 hm).y ((D.fm u).dn i v c g))
      (Formalism.L2.Forms.reGL (CF.rankN D i hm).symm _ (M.dnG i hm v c g).1) (H.vT u v).1) :
    CH.AdI D H u i h1 hm c ((D.fm u).dn i v c g) (M.toMoves.dnG i v c g) v := by
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb (D.sp.X i).frame (M.dnS i v c g).1) _
  rw [M.dnS_eq i hm, hxG_toGLb]
  exact h

theorem hxm_adI_dil (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i)
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm).U ((H.cls u i h1 hm).y c)
      ((H.cls u i h1 hm).y ((D.fm u).dil i v a c))
      (Formalism.L2.Forms.reGL (CF.rankN D i hm).symm _ (M.dilG i hm v a c).1) (H.vT u v).1) :
    CH.AdI D H u i h1 hm c ((D.fm u).dil i v a c) (M.toMoves.dilG i v a c) v := by
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb (D.sp.X i).frame (M.dilS i v a c).1) _
  rw [M.dilS_eq i hm, hxG_toGLb]
  exact h

theorem adjacency_level_zero_up (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (y : ↥(CH.Ld D u 0 c))
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c)
      ((H.lev0 u).y ((D.fm u).up 0 v c ((P 0 (Nat.zero_le _)).pr v c (hxLd 0 (Nat.zero_le _) c y))))
      (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level D.R).symm _ (M.upG 0 (Nat.zero_le _) v c (hxLd 0 (Nat.zero_le _) c y)).1) (H.vT u v).1) :
    CH.Ad0 D H u c ((D.fm u).up 0 v c (hxPr A P 0 v c y)) (M.toMoves.upG 0 v c y) v := by
  rw [hxPr_eq A P 0 (Nat.zero_le _)]
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) (M.upS 0 v c y).1) _
  rw [M.upS_eq 0 (Nat.zero_le _), hxG_toGLb0]
  exact h

theorem adjacency_level_zero_down (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c) ((H.lev0 u).y ((D.fm u).dn 0 v c g))
      (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level D.R).symm _ (M.dnG 0 (Nat.zero_le _) v c g).1) (H.vT u v).1) :
    CH.Ad0 D H u c ((D.fm u).dn 0 v c g) (M.toMoves.dnG 0 v c g) v := by
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) (M.dnS 0 v c g).1) _
  rw [M.dnS_eq 0 (Nat.zero_le _), hxG_toGLb0]
  exact h

theorem adjacency_level_zero_dilation (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls 0)
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c) ((H.lev0 u).y ((D.fm u).dil 0 v a c))
      (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level D.R).symm _ (M.dilG 0 (Nat.zero_le _) v a c).1) (H.vT u v).1) :
    CH.Ad0 D H u c ((D.fm u).dil 0 v a c) (M.toMoves.dilG 0 v a c) v := by
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) (M.dilS 0 v a c).1) _
  rw [M.dilS_eq 0 (Nat.zero_le _), hxG_toGLb0]
  exact h

end Any

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d)

set_option maxHeartbeats 4000000 in

def atTMovesC (u : d.what₂.Word) : AtTMovesC (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) where
  upG := fun i hi v c y => tamG d.sp.cm (stepCrd a hS hH u i hi) (tamMv (Pr := d.Pr) d.W d.lev u i
    ((d.repr u i c).upL v (d.Pr.T u : 𝓞 d.X.E) (tiePr d.sp.cm d.hPr d.σ₀ u (d.repr u i) (stepCrd a hS hH u i hi) v c y)))
  up_tie := fun i hi v c y hy => tam_up (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (stepCrd a hS hH u i hi) v c y hy
  dnG := fun i hi v c g => tamG d.sp.cm (stepCrd a hS hH u i hi) (tamMv (Pr := d.Pr) d.W d.lev u i ((d.repr u i c).dnL v g))
  dn_tie := fun i hi v c g hg => tam_dn (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (stepCrd a hS hH u i hi) v c g hg
  dilG := fun i hi v x c => tamG d.sp.cm (stepCrd a hS hH u i hi) (tamMv (Pr := d.Pr) d.W d.lev u i ((d.repr u i c).dia1 v x))
  dil_tie := fun i hi v x c => tam_dil (Pr := d.Pr) d.W d.lev d.sp.cm d.hPr d.σ₀ u i (stepCrd a hS hH u i hi) v x c

def atTMoves (u : d.what₂.Word) : AtTMoves (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) :=
  (atTMovesC a hS hH u).toMoves

end Rec

section AdRec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d)
  (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)

theorem th_adI (u : d.what₂.Word) (i : ℕ) (hm : i ≤ d.R.m) (v : d.Pr.vT u) (c : StCl (Pr := d.Pr) d.W d.lev u i)
    (d₁ : DecoSet d.X.E (d.R.N i) (d.Pr.vT u) d.Pr.vGs)
    (h : Deco.SameOff (d.Pr.vT u) d.Pr.vGs (tieEV d.sp.cm d.hX d.hPr u v).1 (d.repr u i c).1 d₁.1) :
    Formalism.L2.Herm.AdStep d.sp.cm.sig (d.sp.X i).gram (hermPack hS hP hK u i hm).lev.U ((hermPack hS hP hK u i hm).cls.y c).1
      ((hermPack hS hP hK u i hm).cls.y (clsD (colVal (Pr := d.Pr) d.W u i (d.Pr.vT u) d.Pr.vGs) (d.lev i) d₁)).1
      (Formalism.L2.Forms.reGL (d.sp.X_rank i hm).symm _ (ufGL d.X.E (d.R.N i) (tamMv (Pr := d.Pr) d.W d.lev u i d₁)))
      (tieEV d.sp.cm d.hX d.hPr u v).1 :=
  tam_ad d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (hK u i) (hCrd hS u i hm) _ c _ d₁ h
    ((stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.mv d₁) ((stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.mv_smul d₁)

theorem adjacency_level_zero_tied (u : d.what₂.Word) (v : d.Pr.vT u) (c : StCl (Pr := d.Pr) d.W d.lev u 0)
    (d₁ : DecoSet d.X.E (d.R.N 0) (d.Pr.vT u) d.Pr.vGs)
    (h : Deco.SameOff (d.Pr.vT u) d.Pr.vGs (tieEV d.sp.cm d.hX d.hPr u v).1 (d.repr u 0 c).1 d₁.1) :
    Formalism.L2.Herm.AdStep d.sp.cm.sig d.sp.gram0 (hermPack0 hS hP hK u).lev.U ((hermPack0 hS hP hK u).cls.y c).1
      ((hermPack0 hS hP hK u).cls.y (clsD (colVal (Pr := d.Pr) d.W u 0 (d.Pr.vT u) d.Pr.vGs) (d.lev 0) d₁)).1
      (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level d.R).symm _ (ufGL d.X.E (d.R.N 0) (tamMv (Pr := d.Pr) d.W d.lev u 0 d₁)))
      (tieEV d.sp.cm d.hX d.hPr u v).1 :=
  tam_ad d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) (hCrd0 hS u) _ c _ d₁ h
    ((stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.mv d₁) ((stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.mv_smul d₁)

set_option maxHeartbeats 4000000 in

theorem adTied (O : AtTOwed a hS hH) (hO : O.moves = atTMoves a hS hH) :
    CH.AdTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) := by
  obtain ⟨disc, moves, xp⟩ := O
  obtain rfl : moves = atTMoves a hS hH := hO
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v c y hy
    have hy' := hy
    rw [show (hermAtT a hS hH ⟨disc, atTMoves a hS hH, xp⟩ u).pr 0 v c y = _ from
      hxPr_eq (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) 0 (Nat.zero_le _) v c y] at hy'
    exact adjacency_level_zero_up (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) v c y
      (adjacency_level_zero_tied hS hP hK u v c _ (tam_so_up (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u 0 (stepCrd a hS hH u 0 (Nat.zero_le _)) v c _ hy'))
  · intro u i h1 hm v c y hy
    have hy' := hy
    rw [show (hermAtT a hS hH ⟨disc, atTMoves a hS hH, xp⟩ u).pr i v c y = _ from
      hxPr_eq (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) i hm v c y] at hy'
    exact hxm_adI_up (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) i h1 hm v c y
      (th_adI hS hP hK u i hm v c _ (tam_so_up (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (stepCrd a hS hH u i hm) v c _ hy'))
  · intro u v c g hg
    exact adjacency_level_zero_down (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) v c g
      (adjacency_level_zero_tied hS hP hK u v c _ (tam_so_dn (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr u 0 v c g hg))
  · intro u i h1 hm v c g hg
    exact hxm_adI_dn (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) i h1 hm v c g
      (th_adI hS hP hK u i hm v c _ (tam_so_dn (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr u i v c g hg))
  · intro u v x c
    exact adjacency_level_zero_dilation (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) v x c
      (adjacency_level_zero_tied hS hP hK u v c _ (tam_sameOff_dia (d.R.N 0) (d.Pr.vT u) d.Pr.vGs (d.repr u 0 c) v x (tieEV_over d.sp.cm d.hX d.hPr u v)))
  · intro u i h1 hm v x c
    exact hxm_adI_dil (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) i h1 hm v x c
      (th_adI hS hP hK u i hm v c _ (tam_sameOff_dia (d.R.N i) (d.Pr.vT u) d.Pr.vGs (d.repr u i c) v x (tieEV_over d.sp.cm d.hX d.hPr u v)))

def atTOwedOf (disc : ∀ u, AtTDisc (d.colRec a) u)
    (xp : ∀ u, AtTXp (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)) : AtTOwed a hS hH :=
  ⟨disc, atTMoves a hS hH, xp⟩

end AdRec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQBOpen
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV

section Div

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

set_option maxHeartbeats 2000000 in

theorem qbK_of_div {c : v.adicCompletion F} (hc : c ∈ v.adicCompletionIntegers F) (hc1 : Valued.v c < 1)
    {k : GL (Fin n) (v.adicCompletion F)} (hk : qbDiv c ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) - 1)) : k ∈ qbK c := by
  classical
  let O := v.adicCompletionIntegers F
  have hkint : qbInt (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := fun i j => by
    obtain ⟨z, hz, e⟩ := hk i j
    have : (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j = c * z + (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j := by
      rw [← e, Matrix.sub_apply, sub_add_cancel]
    rw [this]
    exact Subring.add_mem _ (Subring.mul_mem _ hc hz) (qbInt_one i j)
  let kO : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, hkint i j⟩
  have hres : (IsLocalRing.residue O).mapMatrix kO = 1 := by
    ext i j
    obtain ⟨z, hz, e⟩ := hk i j
    have h2 : IsLocalRing.residue O (kO i j - (1 : Matrix (Fin n) (Fin n) O) i j) = 0 := by
      apply glo_res_zero v
      show Valued.v ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j -
        (((1 : Matrix (Fin n) (Fin n) O) i j : O) : v.adicCompletion F)) < 1
      have e1 : (((1 : Matrix (Fin n) (Fin n) O) i j : O) : v.adicCompletion F) = (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j := by
        rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
      rw [e1, ← Matrix.sub_apply, e, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hz)) hc1
    rw [map_sub, sub_eq_zero] at h2
    show IsLocalRing.residue O (kO i j) = (1 : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)) i j
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit kO.det := by
    have h1 : IsLocalRing.residue O kO.det = 1 := by rw [RingHom.map_det, hres, Matrix.det_one]
    by_contra h
    have h2 : kO.det ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 h
    rw [← IsLocalRing.residue_eq_zero_iff] at h2
    rw [h2] at h1
    exact zero_ne_one h1
  have hinv : kO * kO⁻¹ = 1 := Matrix.mul_nonsing_inv kO hdet
  have hmap : (O.subtype).mapMatrix kO = (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := rfl
  have hk1 : (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (O.subtype).mapMatrix kO⁻¹ = 1 := by
    rw [← hmap, ← map_mul, hinv, map_one]
  have hkinv : ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (O.subtype).mapMatrix kO⁻¹ := by
    have := congrArg (fun M => ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * M) hk1
    simp only [mul_one] at this
    rw [← this, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  refine ⟨hkint, fun i j => ?_, hk⟩
  rw [hkinv]
  exact (kO⁻¹ i j).2

end Div

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem qsp_locL_entry {z : Fin n → E ⊗[F] v.adicCompletion F} (hz : z ∈ Formalism.L2.Herm.locL v (stdLat E n)) (i : Fin n) :
    z i ∈ Formalism.BasicNotions.intV E v := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hy i trivial)
    show inclE (F := F) (v.adicCompletion F) (y i) ∈ _
    rw [← hr]
    exact Formalism.MainNotions.Gaps.LG.sc_left_mem v r
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact Subring.add_mem _ hx hy
  | smul a x _ hx => exact Subring.mul_mem _ a.2 hx

theorem qsp_single_locL (j : Fin n) :
    (Pi.single j 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈ Formalism.L2.Herm.locL v (stdLat E n) := by
  classical
  refine Submodule.subset_span ⟨Pi.single j 1, fun l _ => ?_, funext fun i => ?_⟩
  · rw [Pi.single_apply]
    show (if l = j then (1 : E) else 0) ∈ (1 : Submodule (𝓞 E) E)
    by_cases h : l = j
    · rw [if_pos h]; exact Submodule.one_le.1 le_rfl
    · rw [if_neg h]; exact zero_mem _
  · show inclE (F := F) (v.adicCompletion F) ((Pi.single j (1 : E) : Fin n → E) i) = _
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp

end Lat

section Open

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {Q : Finset (Pl E)} (Θ : LevQFam E K n Q)
  (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ)

set_option maxHeartbeats 2000000 in

theorem qbDF_spec (P : Q) : ∃ D : 𝓞 F, D ≠ 0 ∧ D ∈ (underPl F P.1).asIdeal ∧ ∃ w ∈ ((qv F P.1).adicCompletionIntegers F),
    algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) D = qbF hc hQ P (qbD hc Θ hQ hΘ P) * w := by
  obtain ⟨b, hb⟩ := qsp_norm_mem hc (qbPi hc hQ P)
  have hbP : b ∈ (underPl F P.1).asIdeal := by
    show algebraMap (𝓞 F) (𝓞 E) b ∈ P.1.asIdeal
    rw [hb]; exact Ideal.mul_mem_right _ _ (qbPi_spec hc hQ P).1
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, mul_eq_zero] at hb
    rcases hb with h | h
    · exact qbPi_ne hc hQ P h
    · exact (qbPi_spec hc hQ P).2.1 (by rw [h]; exact zero_mem _)
  have hNpos := (qbN_spec Θ hΘ P).1
  refine ⟨b ^ qbN Θ hΘ P, pow_ne_zero _ hb0, Ideal.pow_mem_of_mem _ hbP _ hNpos,
    qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) ^ qbN Θ hΘ P,
    Subring.pow_mem _ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (qbF_int hc hQ P _)) _, ?_⟩
  have hbE : algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) b =
      qbF hc hQ P ((qbPi hc hQ P : 𝓞 E) : E) * qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F ((qv F P.1).adicCompletion F), ← qsp_sp_F hc P.1 _ (qbSp hc hQ P),
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, hb, map_mul, map_mul]
  rw [map_pow, hbE, mul_pow, map_pow]

theorem qbF_d_int (P : Q) : qbF hc hQ P (qbD hc Θ hQ hΘ P) ∈ (qv F P.1).adicCompletionIntegers F := by
  rw [map_pow]
  exact Subring.pow_mem _ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (qbF_int hc hQ P _)) _

theorem qbF_d_lt (P : Q) : Valued.v (qbF hc hQ P (qbD hc Θ hQ hΘ P)) < 1 := by
  rw [map_pow, map_pow]
  exact pow_lt_one₀ zero_le ((qbF_P hc hQ P _).2 (qbPi_spec hc hQ P).1) (Nat.pos_iff_ne_zero.1 (qbN_spec Θ hΘ P).1)

theorem qbU_of_K (P : Q) {k : GL (Fin n) ((qv F P.1).adicCompletion F)} (hk : k ∈ qbK (qbF hc hQ P (qbD hc Θ hQ hΘ P))) :
    k ∈ (qbLoc hc Θ hQ hΘ).U P :=
  ⟨hk.1, hk.2.1, 1, (Θ P).H.one_mem, by simpa using hk⟩

def qbDF (P : Q) : 𝓞 F := Classical.choose (qbDF_spec hc Θ hQ hΘ P)

theorem qbDF_prop (P : Q) : qbDF hc Θ hQ hΘ P ≠ 0 ∧ qbDF hc Θ hQ hΘ P ∈ (underPl F P.1).asIdeal ∧
    ∃ w ∈ ((qv F P.1).adicCompletionIntegers F),
      algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) (qbDF hc Θ hQ hΘ P) = qbF hc hQ P (qbD hc Θ hQ hΘ P) * w :=
  Classical.choose_spec (qbDF_spec hc Θ hQ hΘ P)

set_option maxHeartbeats 4000000 in

theorem qbOpen : QOpen (qbLoc hc Θ hQ hΘ) where
  princ P := by
    classical
    obtain ⟨hD0, -, w, hw, hDw⟩ := qbDF_prop hc Θ hQ hΘ P
    refine ⟨Ideal.absNorm (Ideal.span {qbDF hc Θ hQ hΘ P}), Nat.pos_of_ne_zero fun h => hD0 ?_, fun x _ hy => ?_⟩
    · rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h; exact h
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {qbDF hc Θ hQ hΘ P}))
    apply qbU_of_K hc Θ hQ hΘ P
    apply qbK_of_div (qbF_d_int hc Θ hQ hΘ P) (qbF_d_lt hc Θ hQ hΘ P)
    intro i j
    obtain ⟨z, hz, e⟩ := hy _ (qsp_single_locL (qv F P.1) j)
    have e1 := congrFun e i
    rw [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply, smul_eq_mul] at e1
    set f : E ⊗[F] (qv F P.1).adicCompletion F →+* (qv F P.1).adicCompletion F :=
      (RingHom.fst _ _).comp ((qbLoc hc Θ hQ hΘ).sp P).toRingHom with hf
    have e2 := congrArg f e1
    rw [map_sub, map_mul, map_natCast] at e2
    refine ⟨algebraMap (𝓞 F) _ t * w * f (z i), Subring.mul_mem _ (Subring.mul_mem _ (glo_algMap_int _ t) hw)
      ((((qbLoc hc Θ hQ hΘ).sp_int P (z i)).1 (qsp_locL_entry _ hz i)).1), ?_⟩
    have e3 : ((Ideal.absNorm (Ideal.span {qbDF hc Θ hQ hΘ P}) : ℕ) : (qv F P.1).adicCompletion F) =
        algebraMap (𝓞 F) _ t * (qbF hc hQ P (qbD hc Θ hQ hΘ P) * w) := by
      rw [← hDw, ← map_mul, ht, map_natCast]
    have e4 : f ((Pi.single j (1 : E ⊗[F] (qv F P.1).adicCompletion F) : Fin n → E ⊗[F] (qv F P.1).adicCompletion F) i) =
        (1 : Matrix (Fin n) (Fin n) ((qv F P.1).adicCompletion F)) i j := by
      rw [Pi.single_apply, Matrix.one_apply]; split_ifs <;> simp
    show f ((x : Matrix (Fin n) (Fin n) _) i j) - (1 : Matrix (Fin n) (Fin n) _) i j = _
    rw [← e4, e2, e3]
    ring
  glob := by
    classical
    refine ⟨∏ P ∈ Q.attach, algebraMap (𝓞 F) (𝓞 E) (qbDF hc Θ hQ hΘ P), ?_, fun u _ sa hu P => ?_⟩
    · refine Finset.prod_ne_zero_iff.2 fun P _ h => (qbDF_prop hc Θ hQ hΘ P).1 ?_
      have hinj : Function.Injective (algebraMap (𝓞 F) E) := by
        rw [IsScalarTower.algebraMap_eq (𝓞 F) F E]
        exact (algebraMap F E).injective.comp (IsFractionRing.injective (𝓞 F) F)
      exact hinj (by rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, h, map_zero, map_zero])
    obtain ⟨-, -, w, hw, hDw⟩ := qbDF_prop hc Θ hQ hΘ P
    apply qbU_of_K hc Θ hQ hΘ P
    apply qbK_of_div (qbF_d_int hc Θ hQ hΘ P) (qbF_d_lt hc Θ hQ hΘ P)
    intro i j
    set f : E ⊗[F] (qv F P.1).adicCompletion F →+* (qv F P.1).adicCompletion F :=
      (RingHom.fst _ _).comp ((qbLoc hc Θ hQ hΘ).sp P).toRingHom with hf
    have hφ : ∀ P' : Q, f (inclE (F := F) ((qv F P.1).adicCompletion F) (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) (qbDF hc Θ hQ hΘ P')))) =
        algebraMap (𝓞 F) _ (qbDF hc Θ hQ hΘ P') := fun P' => by
      show qbF hc hQ P _ = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E, qsp_sp_F hc P.1 _ (qbSp hc hQ P),
        ← IsScalarTower.algebraMap_apply]
    have hprod : f (inclE (F := F) ((qv F P.1).adicCompletion F) (algebraMap (𝓞 E) E
        (∏ P' ∈ Q.attach, algebraMap (𝓞 F) (𝓞 E) (qbDF hc Θ hQ hΘ P')))) =
        qbF hc hQ P (qbD hc Θ hQ hΘ P) * (w * ∏ P' ∈ Q.attach.erase P, algebraMap (𝓞 F) _ (qbDF hc Θ hQ hΘ P')) := by
      rw [map_prod, map_prod, map_prod]
      simp only [hφ]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_attach Q P), hDw, mul_assoc]
    refine ⟨w * (∏ P' ∈ Q.attach.erase P, algebraMap (𝓞 F) _ (qbDF hc Θ hQ hΘ P')) * f (prV (E := E) (qv F P.1) (sa i j : E ⊗[F] Formalism.L2.Herm.Af F)),
      Subring.mul_mem _ (Subring.mul_mem _ hw (Subring.prod_mem _ fun P' _ => glo_algMap_int _ _))
        ((((qbLoc hc Θ hQ hΘ).sp_int P _).1 (afsplit_prV_int (qv F P.1) _ (sa i j).2)).1), ?_⟩
    show f (prV (E := E) (qv F P.1) ((u : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j)) - (1 : Matrix (Fin n) (Fin n) _) i j = _
    rw [hu i j, map_add, map_add, map_mul, map_mul]
    have e4 : f (prV (E := E) (qv F P.1) ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j)) = (1 : Matrix (Fin n) (Fin n) _) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [e4, add_sub_cancel_left]
    show f (prV (E := E) (qv F P.1) (inclE (F := F) (Formalism.L2.Herm.Af F) _)) * _ = _
    rw [afsplit_prV_inclE, hprod]
    ring

end Open

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQOrb
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QOrb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

theorem qdf_at_rat (q : QLoc hc n Q Θ) (P : Q) (γ : GL (Fin n) E) : q.at P (bc (iA F E) γ) = bc (q.phi P) γ := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rfl

theorem qdf_at_mul (q : QLoc hc n Q Θ) (P : Q) (x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : q.at P (x * y) = q.at P x * q.at P y := by
  show bc _ (bc _ (x * y)) = _
  rw [map_mul, map_mul]

theorem qdf_at_inv (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : q.at P x⁻¹ = (q.at P x)⁻¹ := by
  show bc _ (bc _ x⁻¹) = _
  rw [map_inv, map_inv]

theorem qdf_levUQ_le (H : Subgroup (GLG E n SG)) (q : QLoc hc n Q Θ) : levUQ hc n ST SG Q H q ≤ levU hc n ST SG H := inf_le_left

theorem qdf_levUQ_at (H : Subgroup (GLG E n SG)) (q : QLoc hc n Q Θ) {κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : κ ∈ levUQ hc n ST SG Q H q) (P : Q) : q.at P κ ∈ q.U P :=
  (Subgroup.mem_iInf.1 h.2) P

theorem qdf_ratio_val (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n) (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    (qdRatio p p' γ hN P).1 = (p'.fr P)⁻¹ * γ * p.fr P := rfl

variable (H : Subgroup (GLG E n SG))

theorem qdf_orbit_of_rel (q : QLoc hc n Q Θ) {x x' : UAd hc n} {p p' : DecoF E n ST SG Q}
    (hx : FrOver q x.1 p) (hx' : FrOver q x'.1 p') (γ : URat hc n) (κ : levUQ hc n ST SG Q H q)
    (e : (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
      (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) :
    ∃ a : UF E n × H × Θ.grp, a.1 = ratHom hc n γ ∧ a.2.1 = levRed hc n ST SG H ⟨_, qdf_levUQ_le H q κ.2⟩ ∧ p' = a • p := by
  have hκ : (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ levU hc n ST SG H := qdf_levUQ_le H q κ.2
  have hd : decoOf ST SG (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((ratHom hc n γ, levRed hc n ST SG H ⟨_, hκ⟩) : UF E n × H) • decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [e]; exact rlc_decoOf_sm hc n ST SG H γ ⟨_, hκ⟩ x
  rw [hx.1, hx'.1] at hd
  have hN : p'.deco.1.N = gmap (ratHom hc n γ).1 p.deco.1.N := by rw [hd]; rfl
  have hinj : ∀ a b : GL (Fin n) E, Formalism.UG.glEquiv a = Formalism.UG.glEquiv b → a = b := fun a b h =>
    Units.ext (Matrix.ext_of_mulVec_single fun j => by
      have := congrArg (fun g : Sp E n ≃ₗ[E] Sp E n => g (Pi.single j 1)) h
      simpa [Formalism.UG.glEquiv] using this)
  have hγ : toGLm E n (ratHom hc n γ).1 = (γ : GL (Fin n) E) :=
    hinj _ _ (by rw [glEquiv_toGLm]; rfl)
  have hθ : ∀ P : Q, qdRatio p p' (ratHom hc n γ).1 hN P ∈ (Θ P).H := by
    intro P
    rw [← q.U_rat P]
    have h1 := hx.2 P
    have h2 := hx'.2 P
    have h3 := qdf_levUQ_at H q κ.2 P
    have hx'P : q.at P (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        bc (q.phi P) (γ : GL (Fin n) E) * q.at P x * (q.at P κ)⁻¹ := by
      rw [e, qdf_at_mul, qdf_at_mul, qdf_at_inv, qdf_at_rat]
    have key : bc (q.phi P) (qGL n (qdRatio p p' (ratHom hc n γ).1 hN P).1) =
        ((bc (q.phi P) (qGL n (p'.fr P)))⁻¹ * q.at P x') * q.at P κ * ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x)⁻¹ := by
      rw [qdf_ratio_val]
      simp only [qGL, map_mul, map_inv]
      rw [hγ, hx'P]
      group
    rw [key]
    exact mul_mem (mul_mem h2 h3) (inv_mem h1)
  refine ⟨(ratHom hc n γ, levRed hc n ST SG H ⟨_, hκ⟩, ⟨fun P => qdRatio p p' (ratHom hc n γ).1 hN P,
    (Subgroup.mem_pi _).2 fun P _ => hθ P⟩), rfl, rfl, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hd
  · funext P
    show p'.fr P = (ratHom hc n γ).1 * p.fr P * ((qdRatio p p' (ratHom hc n γ).1 hN P)⁻¹).1
    rw [Subgroup.coe_inv, qdf_ratio_val]
    group

end QOrb

end Formalism.L2.Col
end
end

