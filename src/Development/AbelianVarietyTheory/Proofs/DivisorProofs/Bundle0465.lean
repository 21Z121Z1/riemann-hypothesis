import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0446
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0447
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionComplexAugmentationQuasiIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupGradedCommOfIsFlip
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.CupFlip
open GlobalTheory.EtC.CupSpec

variable {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} {n m : ℤ}

def phi (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m) (w : ℤ) {N : ℕ} (x : Sx E N U) :
    (Pr N →₀ ℤ) →ₗ[ℤ] Sec (K.X w) U :=
  Finsupp.linearCombination ℤ fun z => sg (m * z.1) • pv μ a b w z.1 z.2.1 (x.along z.2.2.1) (x.along z.2.2.2)

variable (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)

theorem phi_single (w : ℤ) {N : ℕ} (x : Sx E N U) (z : Pr N) (t : ℤ) :
    phi μ a b w x (Finsupp.single z t) = t • sg (m * z.1) • pv μ a b w z.1 z.2.1 (x.along z.2.2.1) (x.along z.2.2.2) :=
  Finsupp.linearCombination_single _ _ _

theorem face_eq {p : ℕ} (x : Sx E (p + 1) U) (i : Fin (p + 2)) : x.face i = x.along (SimplexCategory.δ i) := rfl

theorem along_res {N p : ℕ} {V : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    (x.res g).along θ = (x.along θ).res g :=
  ConcreteCategory.congr_hom ((E.map θ.op).naturality g.op) x

theorem pv_res (w : ℤ) (p r : ℕ) {V : Scheme.{0}} (g : V ⟶ U) (y : Sx E p U) (z : Sx E r U) :
    Sec.res g (pv μ a b w p r y z) = pv μ a b w p r (y.res g) (z.res g) := by
  unfold pv
  split_ifs with h
  · rw [μ.nat, ev_res, ev_res]
  · exact map_zero _

theorem phi_res (w : ℤ) {N : ℕ} {V : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (c : Pr N →₀ ℤ) :
    Sec.res g (phi μ a b w x c) = phi μ a b w (x.res g) c := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]; exact map_zero _
  | add f f' hf hf' => rw [map_add, map_add, ← hf, ← hf']; exact map_add _ _ _
  | single z t =>
    rw [phi_single, phi_single, along_res, along_res, ← pv_res]
    simp only [Sec.res, map_zsmul]

theorem phi_along (w : ℤ) {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (x : Sx E M U) (c : Pr N →₀ ℤ) :
    phi μ a b w (x.along θ) c = phi μ a b w x (Pr.push θ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f f' hf hf' => rw [map_add, map_add, map_add, hf, hf']
  | single z t =>
    rw [Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, phi_single, phi_single, along_along, along_along]

end GlobalTheory.EtC.CupFlip

namespace GlobalTheory.EtC.CupFlip
open GlobalTheory.EtC.CupSpec
variable {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} {n m : ℤ}
variable (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)

theorem phi_d₁ (w : ℤ) {N : ℕ} (x : Sx E N U) (p r : ℕ) (a' : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b' : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    phi μ a b w x (Pr.d₁ ⟨p, r, a', b'⟩) = sg (m * p + m) • bdL (pv μ a b w) p r (x.along a') (x.along b') := by
  cases p with
  | zero =>
    change phi μ a b w x 0 = _
    simp [bdL]
  | succ p =>
    change phi μ a b w x (∑ i : Fin (p + 2), Finsupp.single ⟨p, r, SimplexCategory.δ i ≫ a', b'⟩ ((-1) ^ (i : ℕ))) = _
    have e : sg (m * ((p + 1 : ℕ) : ℤ) + m) = sg (m * p) := by
      rw [show m * ((p + 1 : ℕ) : ℤ) + m = m * p + (m + m) by push_cast; ring, sg_add, sg_add, sg_sq, mul_one]
    rw [map_sum, bdL, e, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [phi_single, face_eq, along_along, smul_comm]

theorem phi_d₂ (w : ℤ) {N : ℕ} (x : Sx E N U) (p r : ℕ) (a' : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b' : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    phi μ a b w x (Pr.d₂ ⟨p, r, a', b'⟩) = sg (m * p) • bdR (pv μ a b w) p r (x.along a') (x.along b') := by
  cases r with
  | zero =>
    change phi μ a b w x 0 = _
    simp [bdR]
  | succ r =>
    change phi μ a b w x (∑ j : Fin (r + 2), Finsupp.single ⟨p, r, a', SimplexCategory.δ j ≫ b'⟩ ((-1) ^ (j : ℕ))) = _
    rw [map_sum, bdR, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [phi_single, face_eq, along_along, smul_comm]

theorem pv_zero_left (w : ℤ) (p r : ℕ) (y : Sx E p U) (z : Sx E r U) :
    pv μ (0 : Cochain ((chains R).obj E) I n) b w p r y z = 0 := by
  unfold pv
  split_ifs
  · rw [ev_zero, map_zero, LinearMap.zero_apply]
  · rfl

theorem pv_zero_right (w : ℤ) (p r : ℕ) (y : Sx E p U) (z : Sx E r U) :
    pv μ a (0 : Cochain ((chains R).obj E) J m) w p r y z = 0 := by
  unfold pv
  split_ifs
  · rw [ev_zero, map_zero]
  · rfl

theorem d_pv_cyc (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (w w' : ℤ) (hw : w + 1 = w')
    (p r : ℕ) (y : Sx E p U) (z : Sx E r U) :
    Sec.map (K.d w w') (pv μ α.1 β.1 w p r y z) =
      -(sg (n + 1) • bdL (pv μ α.1 β.1 w') p r y z) - sg (-(p : ℤ) + n) • sg (m + 1) • bdR (pv μ α.1 β.1 w') p r y z := by
  by_cases h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = w
  · rw [d_pv μ rfl rfl α.1 β.1 w w' hw p r y z h, Cocycle.δ_eq_zero, Cocycle.δ_eq_zero, pv_zero_left, pv_zero_right,
      zero_sub, zero_sub, smul_neg, ← sub_eq_add_neg]
  · have h0 : pv μ α.1 β.1 w p r y z = 0 := dif_neg h
    have hL : bdL (pv μ α.1 β.1 w') p r y z = 0 := by
      cases p with
      | zero => rfl
      | succ p =>
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [pv, dif_neg (by push_cast at h ⊢; omega), smul_zero]
    have hR : bdR (pv μ α.1 β.1 w') p r y z = 0 := by
      cases r with
      | zero => simp [bdR]
      | succ r =>
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [pv, dif_neg (by push_cast at h ⊢; omega), smul_zero]
    rw [h0, hL, hR]
    simp

theorem phi_d (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (w w' : ℤ) (hw : w + 1 = w')
    {N : ℕ} (x : Sx E N U) (c : Pr N →₀ ℤ) :
    Sec.map (K.d w w') (phi μ α.1 β.1 w x c) = sg (n + m) • phi μ α.1 β.1 w' x (Pr.d N c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => rw [map_add, map_add, map_add, smul_add, ← hf, ← hf']; exact map_add _ _ _
  | single z t =>
    obtain ⟨p, r, a', b'⟩ := z
    have e1 : Sec.map (K.d w w') (phi μ α.1 β.1 w x (Finsupp.single ⟨p, r, a', b'⟩ t)) =
        t • sg (m * p) • Sec.map (K.d w w') (pv μ α.1 β.1 w p r (x.along a') (x.along b')) := by
      rw [phi_single]; simp only [Sec.map, map_zsmul]
    rw [e1, d_pv_cyc μ α β w w' hw, Pr.d, Finsupp.linearCombination_single, map_zsmul, map_add, map_zsmul, phi_d₁, phi_d₂]
    dsimp only
    have hm2 := sg_sq m
    simp only [sg_add, sg_neg, sg_one, sg_nat]
    match_scalars <;> first | ring1 | linear_combination (t * sg (m * p) * sg n) * hm2 | linear_combination (-(t * sg (m * p) * sg n)) * hm2

end GlobalTheory.EtC.CupFlip

namespace GlobalTheory.EtC.CupFlip
open GlobalTheory.EtC.CupSpec
variable {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} {n m : ℤ}

theorem sg_eq_of_even (c d : ℤ) (h : Even (c - d)) : sg c = sg d := by
  obtain ⟨e, he⟩ := h
  calc sg c = sg (d + (e + e)) := by rw [show d + (e + e) = c by omega]
    _ = sg d := by rw [sg_add, sg_add, sg_sq, mul_one]

theorem phi_aw {k : ℤ} (hk : n + m = k) {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m}
    {c : Cochain ((chains R).obj E) K k} (hc : μ.IsAW hk a b c) (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (x : Sx E N U) :
    phi μ a b w x (Pr.aw N) = ev c N w h U x := by
  rw [hc N w h U x, Pr.aw, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [phi_single, one_smul]
  dsimp only
  rw [pv_eq μ a b w (p : ℕ) (N - p) _ _ _ _ rfl rfl (by omega), sg_smul]
  rfl

theorem phi_wa {ν : Pair J I K} (hf : μ.IsFlip ν) {k : ℤ} (h' : m + n = k) {a : Cochain ((chains R).obj E) I n}
    {b : Cochain ((chains R).obj E) J m} {c : Cochain ((chains R).obj E) K k} (hc : ν.IsAW h' b a c) (N : ℕ) (w : ℤ)
    (h : -(N : ℤ) + k = w) (x : Sx E N U) :
    phi μ a b w x (Pr.wa N) = sg (n * m) • ev c N w h U x := by
  rw [hc N w h U x, Pr.wa, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [phi_single]
  dsimp only
  rw [pv_eq μ a b w (N - p) (p : ℕ) _ _ _ _ rfl rfl (by have := p.isLt; omega), hf, sg_smul, sg_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [sg_nat, ← sg_add, ← sg_add, ← sg_add]
  refine sg_eq_of_even _ _ ⟨m * ((N - p : ℕ) : ℤ) - n * m, ?_⟩
  push_cast
  ring
  all_goals (have := p.isLt; omega)

end GlobalTheory.EtC.CupFlip

namespace GlobalTheory.EtC.CupFlip
open GlobalTheory.EtC.CupSpec

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a b : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : ev (a - b) p s h U x = ev a p s h U x - ev b p s h U x :=
  map_sub (evHom I n p s h U x) a b

end GlobalTheory.EtC.CupFlip

open GlobalTheory.EtC.CupSpec GlobalTheory.EtC.CupFlip in

theorem GlobalTheory.EtC.Pair.cup_flip : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν →
    ∀ (E : Spc) {n m k : ℤ} (h : n + m = k) (h' : m + n = k) a b,
      μ.cup E h a b = (n * m).negOnePow • ν.cup E h' b a := by
  intro R _ I J K μ ν hf E n m k h h' a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := μ.aw_exists E h α β
  obtain ⟨γ', hγ'⟩ := ν.aw_exists E h' β α
  rw [μ.cup_spec E h α β γ hγ, ν.cup_spec E h' β α γ' hγ']
  obtain ⟨hh, -, hd0, hds⟩ := GlobalTheory.T.exists_alexanderWhitneyDiagonal_swap_homotopy
  obtain ⟨θ, hθ⟩ := ev_exists (R := R) (E := E) (I := K) (n := k - 1)
    (fun N s _ U x => phi μ α.1 β.1 s x (hh N)) (fun N s _ V U g x => phi_res μ α.1 β.1 s g x (hh N))
  have key : δ (k - 1) k θ = sg k • (γ.1 - sg (n * m) • γ'.1) := by
    refine ev_ext _ _ fun N t ht U x => ?_
    rw [ev_zsmul, ev_sub', ev_zsmul]
    cases N with
    | zero =>
      rw [ev_δ_zero (by omega) θ U (t - 1) t (by omega) ht x, hθ, phi_d μ α β (t - 1) t (by omega), hd0, map_sub,
        phi_aw μ h hγ 0 t ht x, phi_wa μ hf h' hγ' 0 t ht x, h]
    | succ N =>
      have hb : phi μ α.1 β.1 t x (Pr.bd (hh N)) =
          ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • ev θ N t (by omega) U (x.face i) := by
        rw [Pr.bd, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul, hθ, face_eq, phi_along]
      rw [ev_δ_succ (by omega) θ U N (t - 1) t (by omega) ht x, hθ, phi_d μ α β (t - 1) t (by omega), ← hb, h, sg_smul,
        ← smul_add, ← map_add, hds, map_sub, phi_aw μ h hγ (N + 1) t ht x, phi_wa μ hf h' hγ' (N + 1) t ht x]
  have hmk : ∀ (c : ℤ) (z : Cocycle ((chains R).obj E) K k), CohomologyClass.mk (c • z) = c • CohomologyClass.mk z :=
    fun c z => map_zsmul (AddMonoidHom.mk' CohomologyClass.mk CohomologyClass.mk_add) c z
  rw [Units.smul_def, show (((n * m).negOnePow : ℤˣ) : ℤ) = sg (n * m) from rfl, ← hmk, ← sub_eq_zero,
    ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨k - 1, by omega, sg k • θ, ?_⟩
  rw [δ_smul, key, smul_smul, sg_sq, one_smul]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormPullbackIsBoundedSection
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix

namespace GlobalTheory.PullBdd

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem castFrame_mem_GG {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {G : Matrix (Fin r) (Fin r) E}
    {p0 : ℕ} {x : Frame Ψ r} (hx : x ∈ GG Ψ G p0) : castFrame h x ∈ GG Ψ' G p0 := by
  subst h; exact hx

theorem castFrame_mem_Bor {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {b : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) : castFrame h b ∈ Bor Ψ' r := by
  subst h; exact hb

theorem bchar_castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (la : Wt Ψ' r) (b : Frame Ψ r) :
    bchar la (castFrame h b) = bchar (castWt h la) b := by
  subst h; rfl

theorem castFrame_rmul {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x b : Frame Ψ r) :
    castFrame h (rmul x b) = rmul (castFrame h x) (castFrame h b) := rfl

theorem castFrame_lact {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (β : GL (Fin r) E) (x : Frame Ψ r) :
    castFrame h (lact β x) = lact β (castFrame h x) := rfl

theorem lact_rmul {Ψ : Finset (E →+* ℂ)} (β : GL (Fin r) E) (x b : Frame Ψ r) :
    lact β (rmul x b) = rmul (lact β x) b := by
  funext τ
  show ((β : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ) =
    (β : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ
  rw [Matrix.mul_assoc]

theorem lact_lact {Ψ : Finset (E →+* ℂ)} (β γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact β (lact γ x) = lact (β * γ) x := by
  funext τ
  show ((β : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
      Matrix (Fin r) (Fin r) ℂ) =
    ((↑(β * γ) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem dmin_lact {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {β : GL (Fin r) E}
    (hβ : ∀ u v, herm G ((β : Matrix (Fin r) (Fin r) E) *ᵥ u) ((β : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm G u v) (x : Frame Ψ r) (τ : Ψ) (i : Fin (r + 1)) :
    dmin G (lact β x) τ i = dmin G x τ i := by
  have e1 : mat (lact β x) τ = (β : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  have e2 : gram τ.1 G (mat (lact β x) τ) = gram τ.1 G (mat x τ) := by
    ext a b
    simp only [gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hβ]
  unfold dmin
  rw [e2]

theorem nfac_cast {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (G : Matrix (Fin r) (Fin r) E)
    (la : Wt Ψ' r) (x : Frame Ψ r) :
    (∏ τ : Ψ', ∏ i : Fin r, ‖dmin G (castFrame h x) τ i.succ / dmin G (castFrame h x) τ i.castSucc‖ ^
      (-(la τ i : ℝ) / 2)) =
    ∏ τ : Ψ, ∏ i : Fin r, ‖dmin G x τ i.succ / dmin G x τ i.castSucc‖ ^
      (-(castWt h la τ i : ℝ) / 2) := by
  subst h; rfl

theorem isBddSec_transport (X Y : Data E r) (hΨ : X.Ψ = Y.Ψ) (hG : X.Gm = Y.Gm) (hp : X.p0 = Y.p0)
    (β : GL (Fin r) E)
    (hβ : ∀ u v, herm Y.Gm ((β : Matrix (Fin r) (Fin r) E) *ᵥ u) ((β : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm Y.Gm u v)
    (hΓ : ∀ γ ∈ X.Γ, β * γ * β⁻¹ ∈ Y.Γ) (la : Wt Y.Ψ r)
    (hχX : ∀ γ ∈ X.Γ, X.χ (castWt hΨ la) γ = 1) (hχY : ∀ γ ∈ Y.Γ, Y.χ la γ = 1)
    (Q : Frame Y.Ψ r → ℂ) (hQ : Y.IsBddSec la Q) :
    X.IsBddSec (castWt hΨ la) (fun x => Q (lact β (castFrame hΨ x))) := by
  obtain ⟨⟨hQd, hQB, hQΓ⟩, C, hC⟩ := hQ
  have hmaps : ∀ x ∈ X.dom, lact β (castFrame hΨ x) ∈ Y.dom := by
    intro x hx
    have h1 := castFrame_mem_GG hΨ hx
    rw [hG, hp] at h1
    exact GlobalTheory.FrameFibre.lact_mem_GG hβ h1
  refine ⟨⟨?_, ?_, ?_⟩, C, fun x hx => ?_⟩
  · have hd : Differentiable ℂ (fun x : Frame X.Ψ r => lact β (castFrame hΨ x)) := by
      rw [differentiable_pi]; intro τ; rw [differentiable_pi]; intro a; rw [differentiable_pi]; intro b
      simp only [lact, castFrame, mat, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
      fun_prop
    exact hQd.comp hd.differentiableOn hmaps
  · intro x hx b hb
    simp only
    rw [castFrame_rmul, lact_rmul, hQB _ (hmaps x hx) _ (castFrame_mem_Bor hΨ hb), bchar_castFrame]
  · intro γ hγ x hx
    simp only
    rw [hχX γ hγ, one_mul, castFrame_lact, lact_lact,
      show β * γ = (β * γ * β⁻¹) * β by group, ← lact_lact, hQΓ _ (hΓ γ hγ) _ (hmaps x hx),
      hχY _ (hΓ γ hγ), one_mul]
  · refine le_trans (le_of_eq ?_) (hC _ (hmaps x hx))
    unfold Data.pnorm
    congr 1
    simp only [dmin_lact hβ]
    rw [← hG]
    exact (nfac_cast hΨ X.Gm la x).symm

end

theorem pull_isBddSec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type)
    [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ),
    F ∈ M.SS la → ∀ (h : U) (c : C),
      (M.comp c).IsBddSec (castWt (M.comp_Ψ c) la) (fun x => M.pull h F c (castFrame (M.comp_Ψ c) x)) := by
  intro E _ _ _ r U C _ _ M la F hF h c
  have hY := (hF (h • c)).1
  exact isBddSec_transport (M.comp c).toData (M.comp (h • c)).toData
    ((M.comp_Ψ c).trans (M.comp_Ψ (h • c)).symm) (by rw [M.comp_Gm, M.comp_Gm])
    (by rw [M.comp_basePoint, M.comp_basePoint]) (M.tr h c) (by rw [M.comp_Gm]; exact M.tr_herm h c)
    (fun γ hγ => (M.tr_conj h c γ).1 hγ) (castWt (M.comp_Ψ (h • c)) la)
    (fun γ hγ => M.χ_one c _ γ hγ) (fun γ hγ => M.χ_one (h • c) _ γ hγ) _ hY

end GlobalTheory.PullBdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthLeDividedPowerContentStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentialOperatorDepth_le_dividedPowerContent : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d n : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (u : ∀ b, Fin (n b) → Fin (d b) → C) (P : MvPolynomial (Σ b, Fin (n b)) C) (D : ℕ), P.IsHomogeneous D → (∀ b, IsSatFrame v (u b)) → depth G (ι := fun b => Fin (n b)) u P ≤ content v P := by
  first | exact @GlobalTheory.FGDepth.DepthLeContent.depth_le_content | exact GlobalTheory.FGDepth.DepthLeContent.depth_le_content | (intros; apply GlobalTheory.FGDepth.DepthLeContent.depth_le_content <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthRestrictColumnsStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentialOperatorDepth_restrict_columns : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (κ' : Type) [Fintype κ'] [DecidableEq κ'] (e : κ' ↪ κ) (P : MvPolynomial (Σ b : κ', ι (e b)) C), depth G u (MvPolynomial.rename (fun x => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) = depth (fun b => G (e b)) (fun b => u (e b)) P := by
  first | exact @GlobalTheory.FGDepth.depth_restrict | exact GlobalTheory.FGDepth.depth_restrict | (intros; apply GlobalTheory.FGDepth.depth_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentValuationDetPowBoundsStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerContentValuation_detPow_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i c : ℕ), content v (detPow C i c) ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) ∧ ((((i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1) : ℝ)) : EReal) ≤ content v (detPow C i c) := by
  first | exact @GlobalTheory.DetPowContent.content_detPow_bounds | exact GlobalTheory.DetPowContent.content_detPow_bounds | (intros; apply GlobalTheory.DetPowContent.content_detPow_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenPartProjectionMatrixMapMulVecOfEigenvector
section
open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

section Scal

variable {B K : Type} [CommRing B] [CommRing K] {n : ℕ} (g : B →+* K) (v : Fin n → K)

theorem algebraMap_map_mulVec (x : B) :
    (algebraMap B (Matrix (Fin n) (Fin n) B) x).map g *ᵥ v = g x • v := by
  ext k
  simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]

theorem map_mul_mulVec_of_scal {X Y : Matrix (Fin n) (Fin n) B} {c d : K}
    (hX : X.map g *ᵥ v = c • v) (hY : Y.map g *ᵥ v = d • v) : (X * Y).map g *ᵥ v = (c * d) • v := by
  rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hY, Matrix.mulVec_smul, hX, smul_smul, mul_comm]

theorem map_sub_mulVec_of_scal {X Y : Matrix (Fin n) (Fin n) B} {c d : K}
    (hX : X.map g *ᵥ v = c • v) (hY : Y.map g *ᵥ v = d • v) : (X - Y).map g *ᵥ v = (c - d) • v := by
  rw [Matrix.map_sub _ (map_sub g), Matrix.sub_mulVec, hX, hY, sub_smul]

theorem map_sum_mulVec_of_scal {ι : Type*} (s : Finset ι) (X : ι → Matrix (Fin n) (Fin n) B) (c : ι → K)
    (h : ∀ x ∈ s, (X x).map g *ᵥ v = c x • v) : (∑ x ∈ s, X x).map g *ᵥ v = (∑ x ∈ s, c x) • v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.map_add _ (map_add g), Matrix.add_mulVec,
      h a (Finset.mem_insert_self _ _), ih (fun x hx => h x (Finset.mem_insert_of_mem hx)), add_smul]

theorem map_list_prod_mulVec_of_fix (L : List (Matrix (Fin n) (Fin n) B))
    (h : ∀ X ∈ L, X.map g *ᵥ v = v) : L.prod.map g *ᵥ v = v := by
  induction L with
  | nil => rw [List.prod_nil, Matrix.map_one _ (map_zero g) (map_one g), Matrix.one_mulVec]
  | cons X L ih =>
    rw [List.prod_cons, Matrix.map_mul, ← Matrix.mulVec_mulVec,
      ih (fun Y hY => h Y (List.mem_cons_of_mem _ hY)), h X (by simp)]

end Scal

theorem projMat_map_mulVec_of_eig : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
    (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K] (g : B →+* K)
    (i : Fin D.a) (v : Fin n → K), (∀ c : 𝓞 D.F, (M c).map g *ᵥ v = g (βB (b.t i c)) • v) →
      (projMat b βB M i).map g *ᵥ v = v := by
  intro p _ D R _ b B _ βB n M K _ g i v hv
  have hα : ∀ j, j ≠ i → (alphaMat b βB M i j).map g *ᵥ v = v := by
    intro j hj
    have hij : i ≠ j := fun h => hj h.symm
    unfold alphaMat
    rw [Finsupp.sum, map_sum_mulVec_of_scal g v _ _
      (fun x => g (βB (comaxC b i j x)) * (g (βB (b.t i x)) - g (βB (b.t j x))))
      (fun x _ => map_mul_mulVec_of_scal g v (algebraMap_map_mulVec g v _)
        (map_sub_mulVec_of_scal g v (hv x) (algebraMap_map_mulVec g v _)))]
    have hs := congrArg (fun y => g (βB y)) (comaxC_spec b hij)
    simp only [Finsupp.sum, map_sum, map_mul, map_sub, map_one] at hs
    rw [hs, one_smul]
  have hlast := map_mul_mulVec_of_scal g v (algebraMap_map_mulVec g v (βB (uInv b)))
    (map_sub_mulVec_of_scal g v (hv D.ω) (algebraMap_map_mulVec g v (βB ((D.tr : R) - b.ρ))))
  have h1 : g (βB (uInv b)) * (g (βB (b.t i D.ω)) - g (βB ((D.tr : R) - b.ρ))) = 1 := by
    have hu := congrArg (fun y => g (βB y)) (uInv_mul b)
    simp only [map_mul, map_sub, map_one, map_intCast, map_ofNat] at hu ⊢
    rw [b.t_ω]
    linear_combination hu
  rw [h1, one_smul] at hlast
  unfold projMat
  rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hlast]
  refine map_list_prod_mulVec_of_fix g v _ ?_
  intro X hX
  rw [List.mem_ofFn] at hX
  obtain ⟨j, rfl⟩ := hX
  split_ifs with h
  · rw [Matrix.map_one _ (map_zero g) (map_one g), Matrix.one_mulVec]
  · exact hα j h

end GlobalTheory.UPel.HT.LieLin.RankIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequenceStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_coefficient_longExactSequence : GlobalTheory.EtC.A7 := by
  first | (exact @GlobalTheory.EtC.coefSeq_exact) | (exact GlobalTheory.EtC.coefSeq_exact) | (intros; apply GlobalTheory.EtC.coefSeq_exact  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionComplexAugmentationQuasiIsoStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCoinductionComplexAugmentation_quasiIso : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R), (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → QuasiIso (coindAug φ J) := by
  first | (exact @GlobalTheory.EtC.coindAug_quasiIso) | (exact GlobalTheory.EtC.coindAug_quasiIso) | (intros; apply GlobalTheory.EtC.coindAug_quasiIso  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_eq_zero_of_simplicialRowExact : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (P : PSh) (g : disc.obj P ⟶ E), IsIso (g.app (op ⦋0⦌)) →
  ∀ (n : ℕ) (x : H R E F n), pull R g F n x = 0 →
  (∀ p : ℕ, p + 1 ≤ n → RowExact R E F ((n : ℤ) - ((p + 1 : ℕ) : ℤ)) p) → x = 0 := by
  first | (exact @GlobalTheory.EtC.vanish_of_rowExact) | (exact GlobalTheory.EtC.vanish_of_rowExact) | (intros; apply GlobalTheory.EtC.vanish_of_rowExact  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocyclesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ cl : ∀ (P : PSh) (n : ℤ) (t : (free R).obj P ⟶ (res R F).X n), t ≫ (res R F).d n (n + 1) = 0 → H R (disc.obj P) F n, (∀ P n x, ∃ t ht, cl P n t ht = x) ∧ (∀ P n t ht t' ht', cl P n t ht = cl P n t' ht' ↔ ∃ y : (free R).obj P ⟶ (res R F).X (n - 1), t = t' + y ≫ (res R F).d (n - 1) n) ∧ (∀ P n, cl P n 0 zero_comp = 0) ∧ ∀ (P P' : PSh) (f : P ⟶ P') n t ht, ∃ h, pull R (disc.map f) F n (cl P' n t ht) = cl P n ((free R).map f ≫ t) h := by
  first | (exact @GlobalTheory.EtC.disc_elt_cls) | (exact GlobalTheory.EtC.disc_elt_cls) | (intros; apply GlobalTheory.EtC.disc_elt_cls <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyStalkLocalClassesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_stalk_local_classes : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (Θ Θ' : Over S ⥤ Spc) (α : Θ ⟶ Θ'), (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F ((Θ).mapCone c)) → (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F ((Θ').mapCone c)) → ∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R (α.app (Over.mk s)) F → ∀ (U : Over S), Etale U.hom → ∀ (g : Over.mk s ⟶ U) (n : ℤ), (∀ x : H R (Θ.obj U) F n, ∃ (V : Over S) (g' : Over.mk s ⟶ V) (h : V ⟶ U) (y : H R (Θ'.obj V) F n), Etale V.hom ∧ g' ≫ h = g ∧ pull R (α.app V) F n y = pull R (Θ.map h) F n x) ∧ ∀ y : H R (Θ'.obj U) F n, pull R (α.app U) F n y = 0 → ∃ (V : Over S) (g' : Over.mk s ⟶ V) (h : V ⟶ U), Etale V.hom ∧ g' ≫ h = g ∧ pull R (Θ'.map h) F n y = 0 := by
  first | (exact @GlobalTheory.EtC.stalk_local_classes) | (exact GlobalTheory.EtC.stalk_local_classes) | (intros; apply GlobalTheory.EtC.stalk_local_classes  <;> assumption)
end

