import Development.EtaleCohomology.TateTwists.Bundle0013
import Development.EtaleCohomology.TateTwists.Bundle0022
import Development.EtaleCohomology.TateTwists.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.EtaleCohomology.TateTwists.Bundle0018
import Development.EtaleCohomology.TateTwists.Bundle0019
import Development.EtaleCohomology.TateTwists.Bundle0023
import Development.EtaleCohomology.TateTwists.Bundle0024
import Development.EtaleCohomology.TateTwists.Bundle0014
import Development.EtaleCohomology.TateTwists.Bundle0028

-- bundled from Development.EtaleCohomology.TateTwists.CcAwFlipPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.cupflip_ev_ext_pf : LateralTheory.EtaleFoundations.cupflip_ev_ext := by
  intro R _ E I n α β hab
  refine Cochain.ext _ _ fun p q hpq => ?_
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨p.natAbs, by omega⟩
    have key : (chainsXIso R E N).inv ≫ α.v _ q hpq = (chainsXIso R E N).inv ≫ β.v _ q hpq := by
      refine (LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R _ _).2.1 _ _ fun U x => ?_
      exact hab N q hpq U x
    simpa using congrArg (fun f => (chainsXIso R E N).hom ≫ f) key
  · have := (LateralTheory.Fin.EtaleSimplicialChainsFreeDescription.intersectionNumber_baseChange R).1 E
    have hz : IsZero (((chains R).obj E).X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    exact hz.eq_of_src _ _

namespace LateralTheory.EtaleFoundations

theorem ev_res' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  have h3 := (LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R (E.obj (op (SimplexCategory.mk p))) (I.X s)).2.2.1 V U g x
  unfold ev
  rw [show Sx.res g x = (E.obj (op (SimplexCategory.mk p))).map g.op x from rfl, ← h3]
  have := congrArg (fun f => (ModuleCat.Hom.hom f) (freeGen R (E.obj (op (SimplexCategory.mk p))) U x))
    (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)
  simpa using this.symm

theorem along_res' {E : Spc} {p N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.along θ).res g = (x.res g).along θ := by
  unfold Sx.along Sx.res
  exact (NatTrans.naturality_apply (E.map θ.op) g.op x).symm

theorem cupflip_eta_mk_pf : cupflip_eta_mk := by
  intro h _ R _ I J K μ E n m k hk α β
  obtain ⟨η, hη⟩ := LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation.intersectionNumber_baseChange R (E := E) (I := K) (n := k - 1)
    (fun N s _ U x => phi μ hk α β x s (h N)) (by
      intro N s hs V U g x
      simp only [phi, Finsupp.sum, Sec.res, map_sum, map_zsmul]
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      unfold phiT
      split_ifs with hw
      · rw [map_zsmul]
        have := μ.nat g _ _ _ (by omega : -(z.1 : ℤ) + n + (-(z.2.1 : ℤ) + m) = s)
          (ev α z.1 _ rfl U (x.along z.2.2.1)) (ev β z.2.1 _ rfl U (x.along z.2.2.2))
        simp only [Sec.res] at this
        have ea := ev_res' α _ _ rfl g (x.along z.2.2.1)
        have eb := ev_res' β _ _ rfl g (x.along z.2.2.2)
        rw [along_res'] at ea eb
        simp only [Sec.res] at ea eb
        rw [this, ea, eb]
      · simp)
  exact ⟨η, fun N s hs U x => hη N s hs U x⟩

end LateralTheory.EtaleFoundations

theorem LateralTheory.EtaleFoundations.cc_aw_flip_of (hst : LateralTheory.EtaleFoundations.cupflip_steen) (hdl : LateralTheory.EtaleFoundations.cupflip_eta_delta) :
    LateralTheory.EtaleFoundations.cc_aw_flip :=
  LateralTheory.EtaleFoundations.cupflip_aw_flip_of hst (LateralTheory.EtaleFoundations.cupflip_homotopy_of LateralTheory.EtaleFoundations.cupflip_ev_ext_pf
    LateralTheory.EtaleFoundations.cupflip_eta_mk_pf hdl)
end

-- bundled from Development.EtaleCohomology.TateTwists.CupflipEtaDeltaPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.AWLeib

namespace LateralTheory.EtaleFoundations.EtaDelta
variable {R : Type} [CommRing R]

theorem along_face {E : Spc} {U : Scheme.{0}} {M p : ℕ} (x : Sx E M U)
    (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk M) (i : Fin (p + 2)) :
    (x.along a).face i = x.along (SimplexCategory.δ i ≫ a) :=
  along_comp x a (SimplexCategory.δ i)

theorem face_along {E : Spc} {U : Scheme.{0}} {M p : ℕ} (x : Sx E (M + 1) U) (i : Fin (M + 2))
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk M) :
    (x.face i).along a = x.along (a ≫ SimplexCategory.δ i) :=
  along_comp x (SimplexCategory.δ i) a

section
variable {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
  (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m)

theorem phi_eq {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c : Pr N →₀ ℤ) :
    phi μ hk α β x w c = Finsupp.linearCombination ℤ (phiT μ hk α β x w) c := by
  rw [Finsupp.linearCombination_apply]; rfl

theorem phiT_face {M : ℕ} {U : Scheme.{0}} (x : Sx E (M + 1) U) (i : Fin (M + 2)) (w : ℤ) (z : Pr M) :
    phiT μ hk α β (x.face i) w z =
      phiT μ hk α β x w ⟨z.1, z.2.1, z.2.2.1 ≫ SimplexCategory.δ i, z.2.2.2 ≫ SimplexCategory.δ i⟩ := by
  simp only [phiT, face_along]

theorem phi_bd {M : ℕ} {U : Scheme.{0}} (x : Sx E (M + 1) U) (w : ℤ) (c : Pr M →₀ ℤ) :
    ∑ i : Fin (M + 2), (-1 : ℤ) ^ (i : ℕ) • phi μ hk α β (x.face i) w c = phi μ hk α β x w (Pr.bd c) := by
  simp only [phi_eq, Pr.bd, map_sum, map_zsmul, Pr.push, Finsupp.lmapDomain_apply,
    Finsupp.linearCombination_mapDomain]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact congrArg _ (funext fun z => phiT_face μ hk α β x i w z)

theorem phiT_Fm {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    phiT μ hk α β x w ⟨p, r, a, b⟩ = ((m * (p : ℤ)).negOnePow : ℤ) • Fm μ α β U w p r (x.along a) (x.along b) := by
  dsimp only [phiT, Fm]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; omega
  · exfalso; omega
  · rw [smul_zero]

end

theorem ev_zero' {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  have := ev_sub' (0 : Cochain ((chains R).obj E) I n) 0 p s h U x
  rwa [sub_self, sub_self] at this

theorem d_ev {E : Spc} {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E) I n) (p : ℕ) (s t : ℤ)
    (hs : -(p : ℤ) + n = s) (hst : s + 1 = t) (U : Scheme.{0}) (y : Sx E p U) :
    Sec.map (I.d s t) (ev α.1 p s hs U y) =
      ((n.negOnePow : ℤˣ) : ℤ) • bd (fun q z => if hh : -(q : ℤ) + n = t then ev α.1 q t hh U z else 0) p y := by
  have h := ev_delta_bd (n := n) (m := n + 1) rfl α.1 p s t hs (by omega) U y
  rw [Cocycle.δ_eq_zero, ev_zero', Int.negOnePow_succ, Units.smul_def, Units.val_neg, neg_smul] at h
  exact add_neg_eq_zero.mp h.symm

theorem bd_zero' {E : Spc} {U : Scheme.{0}} {G : Type*} [AddCommGroup G] (p : ℕ) (y : Sx E p U) :
    bd (E := E) (U := U) (fun _ _ => (0 : G)) p y = 0 := by
  cases p <;> simp [bd]

theorem mul_zsmul_left {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (c : ℤ)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : μ.mul U s t w h (c • a) b = c • μ.mul U s t w h a b := by
  rw [map_zsmul]; rfl

theorem mul_zsmul_right {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (c : ℤ)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : μ.mul U s t w h a (c • b) = c • μ.mul U s t w h a b :=
  map_zsmul _ c b

theorem d_Fm {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m : ℤ} (α : Cocycle ((chains R).obj E) I n)
    (β : Cocycle ((chains R).obj E) J m) (U : Scheme.{0}) (s t : ℤ) (hst : s + 1 = t) (p r : ℕ)
    (y : Sx E p U) (z : Sx E r U) :
    Sec.map (K.d s t) (Fm μ α.1 β.1 U s p r y z) =
      ((n.negOnePow : ℤˣ) : ℤ) • bd (fun q y' => Fm μ α.1 β.1 U t q r y' z) p y +
      ((((-(p : ℤ) + n) + m).negOnePow : ℤˣ) : ℤ) • bd (fun q z' => Fm μ α.1 β.1 U t p q y z') r z := by
  by_cases h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = s
  · have e : Fm μ α.1 β.1 U s p r y z = μ.mul U _ _ s h (ev α.1 p _ rfl U y) (ev β.1 r _ rfl U z) := by
      unfold Fm; rw [dif_pos h]
    rw [e, leib' μ U _ _ s (-(p : ℤ) + n + 1) (-(r : ℤ) + m + 1) t h rfl rfl hst,
      d_ev α p _ _ rfl rfl, d_ev β r _ _ rfl rfl, mul_zsmul_left, mul_zsmul_right, mul_bd_left, mul_bd_right,
      Units.smul_def, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
    congr 2
    · refine bd_congr (fun q y' hq => ?_) y
      unfold Fm
      rw [dif_pos (by omega), dif_pos (by omega)]
      exact mul_congr μ U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · refine bd_congr (fun q z' hq => ?_) z
      unfold Fm
      rw [dif_pos (by omega), dif_pos (by omega)]
      exact mul_congr μ U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · have e : Fm μ α.1 β.1 U s p r y z = 0 := by unfold Fm; rw [dif_neg h]
    have h0 := secmap_zsmul (K.d s t) (0 : ℤ) (0 : Sec (K.X s) U)
    rw [zero_smul, zero_smul] at h0
    rw [e, h0]
    rw [bd_congr (g := fun _ _ => (0 : Sec (K.X t) U)) (fun q y' hq => by unfold Fm; rw [dif_neg (by omega)]) y,
      bd_congr (g := fun _ _ => (0 : Sec (K.X t) U)) (fun q z' hq => by unfold Fm; rw [dif_neg (by omega)]) z,
      bd_zero', bd_zero', smul_zero, smul_zero, add_zero]

theorem secmap_add' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add ((φ.hom.app (op U)).hom) a b

theorem secmap_zero' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  map_zero ((φ.hom.app (op U)).hom)

section
variable {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
  (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)

theorem part1 {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (t : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    (((m * (p : ℤ)).negOnePow : ℤˣ) : ℤ) • (((n.negOnePow : ℤˣ) : ℤ) •
      bd (fun q y' => Fm μ α.1 β.1 U t q r y' (x.along b)) p (x.along a)) =
    ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t) (Pr.d₁ (⟨p, r, a, b⟩ : Pr N)) := by
  cases p with
  | zero => simp [bd, Pr.d₁]
  | succ p =>
    show _ = _ • Finsupp.linearCombination ℤ _
      (∑ i : Fin (p + 2), Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) ((-1 : ℤ) ^ (i : ℕ)))
    simp only [bd, map_sum, Finsupp.linearCombination_single, phiT_Fm, along_face, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    subst hk
    simp only [sign_nat, ← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by push_cast; ring⟩

theorem part2 {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (t : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    (((m * (p : ℤ)).negOnePow : ℤˣ) : ℤ) • (((((-(p : ℤ) + n) + m).negOnePow : ℤˣ) : ℤ) •
      bd (fun q z' => Fm μ α.1 β.1 U t p q (x.along a) z') r (x.along b)) =
    ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t)
      ((-1 : ℤ) ^ p • Pr.d₂ (⟨p, r, a, b⟩ : Pr N)) := by
  cases r with
  | zero => simp [bd, Pr.d₂]
  | succ r =>
    show _ = _ • Finsupp.linearCombination ℤ _ ((-1 : ℤ) ^ p •
      ∑ j : Fin (r + 2), Finsupp.single (⟨p, r, a, SimplexCategory.δ j ≫ b⟩ : Pr N) ((-1 : ℤ) ^ (j : ℕ)))
    simp only [bd, map_zsmul, map_sum, Finsupp.linearCombination_single, phiT_Fm, along_face, Finset.smul_sum,
      smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    subst hk
    simp only [sign_nat, ← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-(p : ℤ), by push_cast; ring⟩

theorem d_phiT {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (s t : ℤ) (hst : s + 1 = t) (z : Pr N) :
    Sec.map (K.d s t) (phiT μ hk α.1 β.1 x s z) =
      ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t)
        (z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂) := by
  obtain ⟨p, r, a, b⟩ := z
  rw [phiT_Fm, secmap_zsmul, d_Fm μ α β U s t hst, smul_add, map_add, smul_add, part1 μ hk α β, part2 μ hk α β]

theorem d_phi {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (s t : ℤ) (hst : s + 1 = t) (c : Pr N →₀ ℤ) :
    Sec.map (K.d s t) (phi μ hk α.1 β.1 x s c) = ((k.negOnePow : ℤˣ) : ℤ) • phi μ hk α.1 β.1 x t (Pr.d N c) := by
  rw [phi_eq, phi_eq]
  refine Finsupp.induction_linear c ?_ ?_ ?_
  · simp only [map_zero, secmap_zero', smul_zero]
  · intro f g hf hg
    rw [map_add, map_add, map_add, secmap_add', hf, hg, smul_add]
  · intro z a
    rw [Finsupp.linearCombination_single, secmap_zsmul, d_phiT μ hk α β x s t hst]
    unfold Pr.d
    rw [Finsupp.linearCombination_single, map_zsmul, smul_comm]

theorem phi_add {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c d : Pr N →₀ ℤ) :
    phi μ hk α.1 β.1 x w (c + d) = phi μ hk α.1 β.1 x w c + phi μ hk α.1 β.1 x w d := by
  simp only [phi_eq, map_add]

theorem phi_sub {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c d : Pr N →₀ ℤ) :
    phi μ hk α.1 β.1 x w (c - d) = phi μ hk α.1 β.1 x w c - phi μ hk α.1 β.1 x w d := by
  simp only [phi_eq, map_sub]

end

end LateralTheory.EtaleFoundations.EtaDelta

open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.EtaDelta in

theorem LateralTheory.EtaleFoundations.cupflip_eta_delta_of : LateralTheory.EtaleFoundations.cupflip_eta_delta := by
  intro h hs R _ I J K μ E n m k hk α β η hη N t ht U x
  cases N with
  | zero =>
    rw [ev_delta_zero (n := k - 1) (by omega) η (-((0 : ℕ) : ℤ) + (k - 1)) t rfl ht U x, hη 0 _ _ U x,
      d_phi μ hk α β x _ t (by omega), hs.2.1, phi_sub]
  | succ M =>
    rw [ev_delta_succ (n := k - 1) (by omega) η M (-((M + 1 : ℕ) : ℤ) + (k - 1)) t rfl ht U x, hη (M + 1) _ _ U x]
    simp only [hη]
    rw [Units.smul_def, phi_bd, d_phi μ hk α β x _ t (by omega), ← smul_add, ← phi_add, hs.2.2 M, phi_sub]
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizEvalDegreeZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_cup_alexanderWhitney_leibniz_eval_degree_zero : EtaleCochainDifferentialEvaluationDegreeZero := by
  intro R _ E I n m hm α U x w w' h h'
  subst h h'
  have hz : IsZero (((chains R).obj E).X (-((0 : ℕ) : ℤ) + 1)) :=
    HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
      have e : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
      omega)
  have hd0 : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) = 0 := hz.eq_of_tgt _ _
  unfold ev
  rw [δ_v n m hm α (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + m) rfl (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + 1)
    (by omega) rfl, hd0, zero_comp, smul_zero, add_zero, ← Category.assoc]
  rfl

theorem etale_cup_alexanderWhitney_leibniz_of_ext_and_succ (h0 : EtaleSimplicialCochainEqOfEvaluationsAgree) (hs : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree) :
    EtaleAlexanderWhitneyCupLeibnizRule :=
  etale_alexander_whitney_leibniz_of_ext_degree_zero_succ h0 etale_cup_alexanderWhitney_leibniz_eval_degree_zero hs

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSteenrodWhitneyAlexanderCompatibilityOfComp
section
namespace LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy
theorem etale_steenrod_acyclic_models_of_components : LateralTheory.EtaleFoundations.SteenPf.leaf_acyc := by
  apply LateralTheory.EtaleFoundations.SteenPf.leaf_acyc_of
theorem etale_steenrod_alexander_whitney_compatibility_of_components : LateralTheory.EtaleFoundations.SteenPf.leaf_aw := by
  apply LateralTheory.EtaleFoundations.AwPf.leaf_aw_of
theorem etale_steenrod_whitney_alexander_compatibility_of_components : LateralTheory.EtaleFoundations.SteenPf.leaf_wa := by
  apply LateralTheory.EtaleFoundations.SteenPf.leaf_wa_of <;> first | exact etale_steenrod_alexander_whitney_compatibility_of_components
theorem etale_steenrod_power_operation_properties_of_components : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := by
  apply LateralTheory.EtaleFoundations.etale_steenrod_prism_homotopy_of_acyclic_alexander_whitney <;> first | exact etale_steenrod_acyclic_models_of_components | exact etale_steenrod_alexander_whitney_compatibility_of_components | exact etale_steenrod_whitney_alexander_compatibility_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := etale_steenrod_power_operation_properties_of_components
end LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistLocalGenerationAndRootCompatOfPart
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

def LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyMultiplesOfGenerator : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (a : Sec (tw q i) U),
    Loc U fun V g => Sec.res g a = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g a = c • twGen i ζ

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange : Prop :=
  ∀ (q : ℕ) [NeZero q] (j : ℤ),
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen j ζ) = twGen j (ζ.map g.appTop.hom)) ∧
    ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), Loc U fun _ g => ∃ c : ℕ, Sec.res g (twGen j ξ) = c • twGen j (ζ.map g.appTop.hom)

namespace LateralTheory.EtaleFoundations.GenIsoSurjPf
theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := by
  simp [Sec.res]

theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x := by
  simp [Sec.map]
end LateralTheory.EtaleFoundations.GenIsoSurjPf

open LateralTheory.EtaleFoundations.GenIsoSurjPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_hits_products_locally (hl : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyMultiplesOfGenerator)
    (hr : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapHitsProductsLocally := by
  intro q _ i j k T μ hk φ hφ U a b
  refine loc_bind' (loc_mono' (loc_and' (hl q i U a) (hl q j U b)) fun V g hab => ?_)
  rcases hab with ⟨ha | ⟨ζ, c, ha⟩, hb | ⟨ξ, d, hb⟩⟩
  · exact loc_top' fun W h => ⟨0, by rw [← res_res, ha]; simp⟩
  · exact loc_top' fun W h => ⟨0, by rw [← res_res, ha]; simp⟩
  · exact loc_top' fun W h => ⟨0, by rw [← res_res (F := tw q j), hb]; simp⟩
  · refine loc_mono' ((hr q j).2 V ζ ξ) fun W h ⟨e, he⟩ => ?_
    refine ⟨(c * (d * e)) • twGen k (ζ.map h.appTop.hom), ?_⟩
    rw [← res_res, ← res_res (F := tw q j), ha, hb, res_nsmul, res_nsmul, he, (hr q i).1, smul_smul,
      map_nsmul', map_nsmul', map_nsmul', map_nsmul', hφ]
    simp only [map_nsmul, LinearMap.smul_apply, smul_smul]
    ring_nf

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_surjective_of_local_and_root (hl : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyMultiplesOfGenerator)
    (hr : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective :=
  LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_locally_surjective_of_pairs (LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_hits_products_locally hl hr)
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTorsionCohomologyPrimaryLocalization
section
namespace LateralTheory.Fin.EtalePrimitiveRootsExistLocally
theorem etale_locally_exists_primitive_root_of_unity : LateralTheory.EtaleFoundations.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder := by
  apply LateralTheory.EtaleFoundations.etale_locally_exists_primitive_root_of_unity_of_invertible_order
theorem etale_torsion_cohomology_primary_localization_kummer : LateralTheory.EtaleFoundations.EtaleLocallyKummerRootsOfUnits := by
  apply LateralTheory.EtaleFoundations.etale_locally_kummer_roots_of_units_of_invertible_order
theorem etale_torsion_cohomology_primary_localization : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally := by
  apply LateralTheory.EtaleFoundations.etale_locally_roots_of_unity_structure_of_exists_and_kummer <;> first | exact etale_locally_exists_primitive_root_of_unity | exact etale_torsion_cohomology_primary_localization_kummer
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally := etale_torsion_cohomology_primary_localization
end LateralTheory.Fin.EtalePrimitiveRootsExistLocally
end

-- bundled from Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfRootListsLocally
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

def MuRootListProductOneSumEtaleLocallyZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (l : List (Prim q Γ(U, ⊤))), (l.map fun ζ => ζ.1).prod = 1 →
    Loc U fun _ g => ((twF q 1).map g.appTop).hom (l.map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0

theorem mu_root_relation_submodule_etale_locally_zero_of_root_lists (h : MuRootListProductOneSumEtaleLocallyZero) : MuRootRelationSubmoduleEtaleLocallyZero := by
  intro q _ U x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact h q U l hl
  | zero => exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨S, hS, hSa⟩ := ha
    obtain ⟨T, hT, hTb⟩ := hb
    refine ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩
    have h1 : ((twF q 1).map g.appTop).hom a = 0 := hSa V g hg.1
    have h2 : ((twF q 1).map g.appTop).hom b = 0 := hTb V g hg.2
    show ((twF q 1).map g.appTop).hom (a + b) = 0
    rw [map_add, h1, h2, add_zero]
  | smul c a _ ha =>
    obtain ⟨S, hS, hSa⟩ := ha
    exact ⟨S, hS, fun V g hg => by
      have h1 : ((twF q 1).map g.appTop).hom a = 0 := hSa V g hg
      show ((twF q 1).map g.appTop).hom (c • a) = 0
      rw [map_smul, h1, smul_zero]⟩

theorem exists_etale_mono_mu_twist_quotient_of_root_lists_locally_zero (h : MuRootListProductOneSumEtaleLocallyZero) : ExistsEtaleMonoMuTwistKillingRootRelations :=
  exists_etale_mono_muTwist_quotient_of_locally_zero etale_sheafify_mono_of_kernel_locally_zero (mu_root_relation_submodule_etale_locally_zero_of_root_lists h)

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.Imports
section
theorem LateralTheory.Fix.EtaleCochainSemilinearMapCompCompatible.intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible :=
  LateralTheory.EtaleFoundations.etale_cohomology_operation_comp_of_image_spec
    (LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_image_spec_of_hyp (by
      have h := LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses.intersectionNumber_baseChange
      unfold LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses at h
      exact h))
end

-- bundled from Development.EtaleCohomology.TateTwists.MapMapEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.columnPf

def kerLoc : Prop :=
  ∀ (R : Type) [CommRing R] (M : Shv R) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ M.obj),
    (∀ (U : Scheme.{0}) (y : Sec M U), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = Sec.res g y) →
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) →
    ∀ (G : Shv R) (V : Scheme.{0}) (u : Sec G V ⊗[ULift.{1} R] P.obj (op V)),
      TensorProduct.map LinearMap.id (φ.app (op V)).hom u = 0 →
      Loc V fun _ k => TensorProduct.map (G.obj.map k.op).hom (P.map k.op).hom u = 0

theorem map_map_eq {S : Type*} [CommRing S] {A B C D A' B' C' D' : Type*} [AddCommGroup A] [Module S A]
    [AddCommGroup B] [Module S B] [AddCommGroup C] [Module S C] [AddCommGroup D] [Module S D]
    [AddCommGroup A'] [Module S A'] [AddCommGroup B'] [Module S B'] [AddCommGroup C'] [Module S C']
    [AddCommGroup D'] [Module S D']
    (f1 : A →ₗ[S] A') (f2 : A' →ₗ[S] C) (f1' : A →ₗ[S] C') (f2' : C' →ₗ[S] C)
    (g1 : B →ₗ[S] B') (g2 : B' →ₗ[S] D) (g1' : B →ₗ[S] D') (g2' : D' →ₗ[S] D)
    (hf : f2 ∘ₗ f1 = f2' ∘ₗ f1') (hg : g2 ∘ₗ g1 = g2' ∘ₗ g1') (x : A ⊗[S] B) :
    TensorProduct.map f2 g2 (TensorProduct.map f1 g1 x) = TensorProduct.map f2' g2' (TensorProduct.map f1' g1' x) := by
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hf, hg, TensorProduct.map_comp, LinearMap.comp_apply]

end LateralTheory.EtaleFoundations.columnPf

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.lift_of (hK : kerLoc) : lift := by
  classical
  intro R _ M P φ hsurj hker F G δ U x hx
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  refine loc_bind (loc_finset S fun i _ => hsurj U i.2) ?_
  intro V g hV
  choose p hp using hV
  let x' : Sec F V ⊗[ULift.{1} R] P.obj (op V) := ∑ i ∈ S.attach, (F.obj.map g.op).hom i.1.1 ⊗ₜ p i.1 i.2
  have h1 : TensorProduct.map LinearMap.id (φ.app (op V)).hom x' =
      TensorProduct.map (F.obj.map g.op).hom (M.obj.map g.op).hom x := by
    rw [hS, map_sum, map_sum, ← Finset.sum_attach S]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [hp i.1 i.2]
  have nat : ∀ {V' V : Scheme.{0}} (k : V' ⟶ V), (G.obj.map k.op).hom ∘ₗ (δ.hom.app (op V)).hom =
      (δ.hom.app (op V')).hom ∘ₗ (F.obj.map k.op).hom := fun k => by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, δ.hom.naturality]
  have h2 : TensorProduct.map LinearMap.id (φ.app (op V)).hom
      (TensorProduct.map (δ.hom.app (op V)).hom LinearMap.id x') = 0 := by
    rw [map_map_eq (f1 := (δ.hom.app (op V)).hom) (f2 := LinearMap.id) (g1 := LinearMap.id) (g2 := (φ.app (op V)).hom)
      (f1' := LinearMap.id) (f2' := (δ.hom.app (op V)).hom) (g1' := (φ.app (op V)).hom) (g2' := LinearMap.id)
      (by simp) (by simp), h1,
      map_map_eq (f1 := (F.obj.map g.op).hom) (f2 := (δ.hom.app (op V)).hom) (g1 := (M.obj.map g.op).hom)
      (g2 := LinearMap.id) (f1' := (δ.hom.app (op U)).hom) (f2' := (G.obj.map g.op).hom) (g1' := LinearMap.id)
      (g2' := (M.obj.map g.op).hom) (nat g).symm (by simp), hx, map_zero]
  refine loc_mono (hK R M P φ hsurj hker G V _ h2) ?_
  intro W k hk
  refine ⟨TensorProduct.map (F.obj.map k.op).hom (P.map k.op).hom x', ?_, ?_⟩
  · rw [map_map_eq (f1 := (F.obj.map k.op).hom) (f2 := (δ.hom.app (op W)).hom) (g1 := (P.map k.op).hom)
      (g2 := LinearMap.id) (f1' := (δ.hom.app (op V)).hom) (f2' := (G.obj.map k.op).hom) (g1' := LinearMap.id)
      (g2' := (P.map k.op).hom) (nat k).symm (by simp), hk]
  · have hφ : (φ.app (op W)).hom ∘ₗ (P.map k.op).hom = (M.obj.map k.op).hom ∘ₗ (φ.app (op V)).hom := by
      rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, φ.naturality]
    rw [map_map_eq (f1 := (F.obj.map k.op).hom) (f2 := LinearMap.id) (g1 := (P.map k.op).hom)
      (g2 := (φ.app (op W)).hom) (f1' := LinearMap.id) (f2' := (F.obj.map k.op).hom) (g1' := (φ.app (op V)).hom)
      (g2' := (M.obj.map k.op).hom) (by simp) hφ, h1, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp]

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.column_of' (hK : kerLoc) : LateralTheory.EtaleFoundations.acyc.column :=
  LateralTheory.EtaleFoundations.acyc.column_of_cut (lift_of hK) kill_of
end

