import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0137
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0142
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0089
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.Bundle0002
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)
open GlobalTheory.CompanionTheory.CocProd (tele sa_val)
open GlobalTheory.CompanionTheory.TowerEnd (Q dQ val Vals cl d_cl dQ_apply)

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm.Coc

local macro "fa" : tactic =>
  `(tactic| (simp only [sa_val, Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero]; split_ifs <;> omega))

theorem alt_sum {B : Type*} [CommRing B] {j : ℕ} (w : Fin j → Fin (j + 2) → B) :
    ∑ i : Fin (j + 2), (-1 : B) ^ (i : ℕ) *
      ∏ k : Fin j, (w k (i.succAbove k.succ) - w k (i.succAbove k.castSucc)) = 0 := by
  classical
  set u : Fin j → B := fun k => w k k.succ.castSucc - w k k.castSucc.castSucc with hu
  set v : Fin j → B := fun k => w k k.succ.succ - w k k.succ.castSucc with hv
  set P : ℕ → B := fun n => ∏ k : Fin j, if (k : ℕ) < n then u k else v k with hP
  set T : Fin (j + 2) → B := fun i =>
    ∏ k : Fin j, (w k (i.succAbove k.succ) - w k (i.succAbove k.castSucc)) with hT
  have cg : ∀ (k : Fin j) {p q p' q' : Fin (j + 2)}, (p : ℕ) = p' → (q : ℕ) = q' →
      w k p - w k q = w k p' - w k q' := by
    intro k p q p' q' h h'
    rw [Fin.ext h, Fin.ext h']
  have hT0 : T (Fin.castSucc 0) = P 0 := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Nat.not_lt_zero, if_false]
    refine cg k ?_ ?_ <;> fa
  have hTl : T (Fin.last (j + 1)) = P j := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [k.2, if_true]
    refine cg k ?_ ?_ <;> fa
  have hTi : ∀ i : Fin j, T i.succ.castSucc = P (i + 1) + P i := by
    intro i
    have hPa : P (i + 1) = u i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i + 1 then u k else v k) (Finset.mem_univ i)
      simp only [Nat.lt_add_one, if_true] at this
      exact this.symm
    have hPb : P i = v i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i then u k else v k) (Finset.mem_univ i)
      simp only [lt_irrefl, if_false] at this
      exact this.symm
    have hTa : T i.succ.castSucc = (u i + v i) * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => w k (i.succ.castSucc.succAbove k.succ) -
        w k (i.succ.castSucc.succAbove k.castSucc)) (Finset.mem_univ i)
      refine this.symm.trans ?_
      congr 1
      · have e : u i + v i = w i i.succ.succ - w i i.castSucc.castSucc := by
          rw [hu, hv]; ring
        rw [e]
        refine cg i ?_ ?_ <;> fa
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
        split_ifs with h
        · refine cg k ?_ ?_ <;> fa
        · refine cg k ?_ ?_ <;> fa
    have hE : ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) =
        ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
      have : (k : ℕ) < i + 1 ↔ (k : ℕ) < i := by omega
      simp only [this]
    rw [hTa, hPa, hPb, hE]
    ring
  change ∑ i : Fin (j + 2), (-1 : B) ^ (i : ℕ) * T i = 0
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hint : ∑ i : Fin j, (-1 : B) ^ ((i.succ.castSucc : Fin (j + 2)) : ℕ) * T i.succ.castSucc =
      ∑ m ∈ Finset.range j, (-1 : B) ^ (m + 1) * (P (m + 1) + P m) := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => (-1 : B) ^ (m + 1) * (P (m + 1) + P m)) j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hTi]
    simp only [Fin.val_castSucc, Fin.val_succ]
  rw [hint, hT0, hTl]
  simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_last, pow_zero]
  linear_combination tele P j

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def vt (c : ∀ T : C, Φ.A.obj T) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) :
    Φ.A.obj (s.obj (Fin.last n)) :=
  (Φ.A.map (s.map (homOfLE (Fin.le_last p)))).hom (c (s.obj p))

theorem vt_last (c : ∀ T : C, Φ.A.obj T) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1))
    (hp : p = Fin.last n) : vt c s p = c (s.obj (Fin.last n)) := by
  subst hp
  have : (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) = 𝟙 _ := Subsingleton.elim _ _
  unfold vt
  rw [this, s.map_id]
  simp

theorem face_vt (c : ∀ T : C, Φ.A.obj T) {j : ℕ} (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (Φ.A.map (toLast i s)).hom (c ((face i s).obj (Fin.last j))) = vt c s (i.succAbove (Fin.last j)) := rfl

theorem face_wz {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T) (I : Fin j → Fin d)
    (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (Φ.A.map (toLast i s)).hom (wz u I (face i s)) =
      ∏ k : Fin j, (vt (u (I k)) s (i.succAbove k.succ) - vt (u (I k)) s (i.succAbove k.castSucc)) := by
  unfold wz
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [GlobalTheory.CompanionTheory.CocProd.map_map]
  have e : (face i s).map (homOfLE (Fin.le_last k.succ)) ≫ toLast i s =
      s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [e, map_sub, GlobalTheory.CompanionTheory.CocProd.map_map]
  have e2 : (face i s).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le) ≫
      s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) =
      s.map (homOfLE (Fin.le_last (i.succAbove k.castSucc))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [e2]
  rfl

theorem d_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    (y : ∀ T : C, Φ.A.obj T) (hy : ∀ {T T' : C} (φ : T ⟶ T'), y T' - (Φ.A.map φ).hom (y T) ∈ Φ.J.S T')
    (I : Fin j → Fin d) (s : ComposableArrows C (j + 1)) :
    ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
      (wz u I (face i s) * y ((face i s).obj (Fin.last j))) ∈ (Fil ((j : ℤ) + 1)).S _ := by
  set Y := y (s.obj (Fin.last (j + 1))) with hY
  set T : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    ∏ k : Fin j, (vt (u (I k)) s (i.succAbove k.succ) - vt (u (I k)) s (i.succAbove k.castSucc)) with hT
  set V : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    vt y s (i.succAbove (Fin.last j)) with hV
  have hVY : ∀ i : Fin (j + 1), V i.castSucc = Y := by
    intro i
    refine vt_last y s _ (Fin.ext ?_)
    have := i.2
    rw [sa_val]
    simp only [Fin.val_last, Fin.val_castSucc]
    split_ifs <;> omega
  have hsum : ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
      (wz u I (face i s) * y ((face i s).obj (Fin.last j))) =
      (-1) ^ j * (T (Fin.last (j + 1)) * (Y - V (Fin.last (j + 1)))) := by
    have hterm : ∀ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
        (wz u I (face i s) * y ((face i s).obj (Fin.last j))) = (-1) ^ (i : ℕ) * (T i * V i) := by
      intro i
      rw [map_mul, face_wz, face_vt, zsmul_eq_mul]
      push_cast
      rfl
    have h0 := alt_sum (B := Φ.A.obj (s.obj (Fin.last (j + 1)))) (j := j) (fun k p => vt (u (I k)) s p)
    change ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) * T i = 0 at h0
    rw [Fin.sum_univ_castSucc] at h0
    rw [Finset.sum_congr rfl fun i _ => hterm i, Fin.sum_univ_castSucc]
    have h1 : ∑ i : Fin (j + 1), (-1) ^ ((i.castSucc : Fin (j + 2)) : ℕ) * (T i.castSucc * V i.castSucc) =
        (∑ i : Fin (j + 1), (-1) ^ ((i.castSucc : Fin (j + 2)) : ℕ) * T i.castSucc) * Y := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hVY]
      ring
    rw [h1]
    simp only [Fin.val_last] at h0 ⊢
    linear_combination Y * h0
  rw [hsum]
  refine Ideal.mul_mem_left _ _ ?_
  have hA : T (Fin.last (j + 1)) ∈ (Fil (j : ℤ)).S _ := by
    have := (Fil (j : ℤ)).map_mem (toLast (Fin.last (j + 1)) s) (wz_mem hF u hu I (face (Fin.last (j + 1)) s))
    rwa [face_wz] at this
  have hB : Y - V (Fin.last (j + 1)) ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    have e : (((1 : ℕ) : ℤ)) = 1 := rfl
    rw [e, hF.one]
    have h := hy (s.map (homOfLE (show (Fin.last j).castSucc ≤ Fin.last (j + 1) from Fin.le_last _)))
    have e2 : V (Fin.last (j + 1)) = (Φ.A.map (s.map (homOfLE (show (Fin.last j).castSucc ≤ Fin.last (j + 1) from Fin.le_last _)))).hom
        (y (s.obj (Fin.last j).castSucc)) := by
      have : (Fin.last (j + 1)).succAbove (Fin.last j) = (Fin.last j).castSucc := Fin.succAbove_last_apply _
      simp only [hV, vt]
      rw [this]
    rw [e2]
    exact h
  have h := hF.mul j 1 _ hA hB
  have e : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
  rwa [e] at h

end GlobalTheory.CompanionTheory.GrForm.Coc

open GlobalTheory.CompanionTheory.GrForm.Coc in

theorem GlobalTheory.CompanionTheory.GrForm.stCocycle : GlobalTheory.CompanionTheory.GrForm.StCocycle := by
  intro R _ C _ Φ Fil hF d j u hu y hy I
  let z : Q Φ.A j := fun s => (wz u I s * y (s.obj (Fin.last j)) : Φ.A.obj (s.obj (Fin.last j)))
  have hz : Vals (Fil j) z := fun s => Ideal.mul_mem_right _ _ (wz_mem hF u hu I s)
  refine ⟨cl (Fil j) (Fil ((j : ℤ) + 1)) z hz, ?_, fun s => rfl⟩
  rw [d_cl]
  funext s
  apply Subtype.ext
  change Ideal.Quotient.mk _ (val (dQ Φ.A j z) s) = 0
  rw [dQ_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (d_mem hF u hu y hy I s)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormRestrict
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lift_cocycle_mem {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) {Q : ObjectProperty (Thick (LL q))} (hQ : ∀ T, Q T → InU W T) (i : Fin d)
    {T T' : Q.FullSubcategory} (φ : T ⟶ T') :
    (show (sP Q).A.obj T' from u i T'.obj) - ((sP Q).A.map φ).hom (show (sP Q).A.obj T from u i T.obj) ∈ (sP Q).J.S T' := by
  have h := hQ _ T.property
  have h' := hQ _ T'.property
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  refine Ideal.Quotient.eq.1 ?_
  rw [hu i T'.obj h', ev_nat φ.hom h h' (t i), ← hu i T.obj h]
  rfl

theorem lft_res_sub_mem {W W' : X.Opens} (hW : W' ≤ W) (T : Thick (LL q)) (h : InU W T) (h' : InU W' T) (f : Γ(X, W)) :
    lft W T f - lft W' T (rs hW f) ∈ T.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [lft_spec T h f, lft_spec T h' (rs hW f), ev_res hW T h h' f]

theorem stRes : StRes := by
  intro O _ X q W W' hW d t u hu P P' hPP hP hP' r x c hc
  obtain ⟨f, hf, rfl, hz⟩ := hc
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P'
  have hP'W : ∀ T, P' T → InU W T := fun T h => hP T (hPP T h)
  refine ⟨(resU (GF q r) hPP).pullC r f, ?_, rfl, ?_⟩
  · have := (resU (GF q r) hPP).d_pullC r f
    refine this.trans ?_
    have hf' : CH.d (P.ι ⋙ GF q r) r f = 0 := hf
    rw [hf', map_zero]
  · intro s
    refine (hz (s ⋙ ObjectProperty.ιOfLE hPP)).trans ?_
    refine Ideal.Quotient.eq.2 ?_
    have hdiff : ∀ I : Idx r d,
        wz (Φ := sP P') (fun i T => u i T.obj) I.1 s *
          ((show (sP P').A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) -
            (show (sP P').A.obj (s.obj (Fin.last r)) from lft W' (s.obj (Fin.last r)).obj (rs hW (x I)))) ∈
          (sFil P' ((r : ℤ) + 1)).S (s.obj (Fin.last r)) := by
      intro I
      have hw := wz_mem hF (fun i T => u i T.obj)
        (fun i {T T'} φ => lift_cocycle_mem hu hP'W i φ) I.1 s
      have hδ : (show (sP P').A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) -
          (show (sP P').A.obj (s.obj (Fin.last r)) from lft W' (s.obj (Fin.last r)).obj (rs hW (x I))) ∈
          (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) := by
        have e : (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) = (sP P').J.S (s.obj (Fin.last r)) := hF.one _
        rw [e]
        exact lft_res_sub_mem hW _ (hP'W _ (s.obj (Fin.last r)).property) (hP' _ (s.obj (Fin.last r)).property) (x I)
      have := hF.mul r 1 _ hw hδ
      simpa using this
    have hsum := Ideal.sum_mem _ (t := Finset.univ) (fun I _ => hdiff I)
    simp only [mul_sub, Finset.sum_sub_distrib] at hsum
    exact hsum

end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormSmul
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrFormSmul
open GlobalTheory.CompanionTheory.GrForm

theorem rep_smul {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j} (r : R)
    (h : Rep a b z c) (hz : ∀ s, z' s - r • z s ∈ b.S _) : Rep a b z' (r • c) := by
  obtain ⟨f, hf, rfl, hfz⟩ := h
  refine ⟨r • f, by rw [map_smul, hf, smul_zero], rfl, fun s => ?_⟩
  rw [Ideal.Quotient.eq.mpr (hz s), ← Ideal.Quotient.mkₐ_eq_mk R, map_smul, Ideal.Quotient.mkₐ_eq_mk, ← hfz s]
  rfl

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lft_str_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (a : O) (f : Γ(X, W)) :
    lft W T (strV q W a * f) - T.i a * lft W T f ∈ T.J := by
  rw [← Ideal.Quotient.eq, lft_spec T h, map_mul, map_mul, lft_spec T h, ev_str T h]

theorem lift_nat {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) (i : Fin d) {T T' : Thick (LL q)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T') :
    u i T' - φ.φ (u i T) ∈ T'.J := by
  rw [← Ideal.Quotient.eq, hu i T' h', ev_nat φ h h', ← hu i T h, Ideal.quotientMap_mk]

private theorem mul_mem_sFil_succ_of_mem_sFil_of_mem_J {P : ObjectProperty (Thick (LL q))} {r : ℕ} (T : P.FullSubcategory)
    {y z : T.obj.B} (hy : y ∈ (sFil P (r : ℤ)).S T) (hz : z ∈ T.obj.J) :
    y * z ∈ (sFil P ((r : ℤ) + 1)).S T := by
  have h1 : z ∈ pdP T.obj.δ 1 := by
    have := GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP T.obj.δ 1 hz
    rwa [T.obj.δ.dpow_one hz] at this
  exact GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.obj.δ r 1 (Ideal.mul_mem_mul (show y ∈ pdP T.obj.δ r from hy) h1)

theorem stSmul : StSmul := by
  intro O _ X q W d t u hu P hP r x c a hc
  unfold Rp at hc ⊢
  refine rep_smul _ _ a hc (fun s => ?_)
  have hw : ∀ I : Fin r → Fin d, wz (Φ := sP P) (fun i T => u i T.obj) I s ∈ (sFil P (r : ℤ)).S (s.obj (Fin.last r)) :=
    fun I => wz_mem (GlobalTheory.CompanionTheory.DPFil.isFil_sFil P) _
      (fun i T T' φ => lift_nat hu i (P.ι.map φ) (hP _ T.property) (hP _ T'.property)) I s
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ (fun I _ => ?_)
  rw [← mul_smul_comm, ← mul_sub]
  exact mul_mem_sFil_succ_of_mem_sFil_of_mem_J _ (hw _) (lft_str_sub _ (hP _ (s.obj (Fin.last r)).property) a (x I))

end GlobalTheory.CompanionTheory.GrFormSmul
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVanishOfFrame
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

theorem isLift_lft {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) : IsLift (q := q) W t (fun i T => lft W T (t i)) :=
  fun i T h => lft_spec T h (t i)

theorem rep_zero {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {j : ℕ}
    (c : CH.H (sq a b) j) (h : Rep a b (fun s => 0) c) : c = 0 := by
  obtain ⟨f, hf, rfl, hz⟩ := h
  have e : f = 0 := by
    funext s
    apply Subtype.ext
    rw [show (show sqM a b _ from f s).1 = _ from hz s]
    simp
  subst e
  rfl

theorem van : StFrame → CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → StVan := by
  intro hFr hL hP O _ l s hb X q W d c r j hrs hjr
  obtain ⟨E, σ, θ, hGr, hbot, -, -, -⟩ := hFr l s hb q c _ (isLift_lft W c.t)
  obtain ⟨Q, hQ⟩ := hP (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  have hCr : ∀ r' ≤ (r : ℤ) + 1, Q.Crit (sFil (SS q l s W)) r' := fun r' h => (hQ r' (by omega)).1
  have key := hL Q (GlobalTheory.CompanionTheory.DPFil.isFil_sFil (SS q l s W)) E σ hGr (r : ℤ) hCr j
  rcases lt_or_gt_of_ne hjr with hlt | hlt
  · obtain ⟨h1, -⟩ := key.2 (r - j) (by omega)
    have all : ∀ cl : CH.H (gr (sFil (SS q l s W)) (r : ℤ)) j, cl = 0 := by
      intro cl
      obtain ⟨x, hx, hR⟩ := h1 cl
      have x0 : ∀ I, x I = 0 := fun I => by
        have h := hx I
        rw [hbot (r - j) (by omega)] at h
        exact h
      have e : (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) = fun s => 0 := by
        funext s
        refine Finset.sum_eq_zero fun I _ => ?_
        simp [x0, Frame.form]
      rw [e] at hR
      exact rep_zero _ _ cl hR
    exact ⟨fun a b => (all a).trans (all b).symm⟩
  · exact key.1 (by exact_mod_cast hlt)

end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraCharacter
section
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.FinGLChar

theorem mul_mul_eq_iff {G : Type} [Group G] (a x g : G) :
    a * (x * g) = x ↔ a⁻¹ = x * g * x⁻¹ := by
  constructor
  · intro h
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    rw [← mul_assoc, ← mul_assoc, mul_assoc a x g, h, mul_inv_cancel]
  · intro h
    have e : a = (x * g * x⁻¹)⁻¹ := by rw [← h, inv_inv]
    rw [e]
    group

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

theorem trace_infl (p : parab K b) :
    LinearMap.trace ℂ (PiTensorProduct ℂ fun c => (lam c : Type)) (infl K b lam p) =
      hcFun b (fun c => (lam c).character) p.1 := by
  unfold hcFun infl
  rw [PI.SerBridgeGLW.trace_piTensorMap]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [blkGL, dif_pos p.2]
  rfl

theorem character_hcRep :
    (hcRep K b lam).character = indF (parab K b) (hcFun b fun c => (lam c).character) := by
  classical
  funext g
  have : FiniteDimensional ℂ (PiTensorProduct ℂ fun c => (lam c : Type)) :=
    Module.Finite.of_basis (Basis.piTensorProduct fun c => Module.finBasis ℂ (lam c))
  let _ : Fintype (parab K b) := Fintype.ofFinite _
  have h1 : (hcRep K b lam).character g = LinearMap.trace ℂ _
      (Representation.coind (parab K b).subtype (PI.SerBridgeGLW.inflRep K b lam) g) := rfl
  have h := GlobalTheory.BadShare.trace_coind_mul_card (parab K b).subtype (PI.SerBridgeGLW.inflRep K b lam) g
  rw [← h1] at h
  have hc : (Fintype.card (parab K b) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  unfold indF
  rw [Nat.card_eq_fintype_card, eq_inv_mul_iff_mul_eq₀ hc, mul_comm, h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x * g * x⁻¹ ∈ parab K b
  · have key : ∀ γ : parab K b, (parab K b).subtype γ * (x * g) = x ↔ γ = (⟨_, hx⟩ : parab K b)⁻¹ := by
      intro γ
      rw [mul_mul_eq_iff]
      constructor
      · intro e
        refine Subtype.ext ?_
        show (γ : GL ι K) = (x * g * x⁻¹)⁻¹
        rw [← e]
        simp
      · rintro rfl
        exact inv_inv _
    simp only [key]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos hx, inv_inv]
    exact trace_infl b lam _
  · rw [if_neg hx]
    refine Finset.sum_eq_zero fun γ _ => if_neg fun e => hx ?_
    rw [← (mul_mul_eq_iff _ x g).1 e]
    exact (parab K b).inv_mem γ.2

def leviHom (c : Fin s) : parab K b →* GL {i // b i = c} K where
  toFun := levi K b c
  map_one' := PI.SerBridgeGLW.levi_one' K b c
  map_mul' := PI.SerBridgeGLW.levi_mul' K b c

theorem isClassOn_hcFun :
    IsClassOn (parab K b) (hcFun b fun c => (lam c).character) := by
  intro x hx h hh
  have hm : x * h * x⁻¹ ∈ parab K b := (parab K b).mul_mem ((parab K b).mul_mem hx hh) ((parab K b).inv_mem hx)
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [blkGL, blkGL, dif_pos hm, dif_pos hh]
  have e : (⟨x * h * x⁻¹, hm⟩ : parab K b) = ⟨x, hx⟩ * ⟨h, hh⟩ * (⟨x, hx⟩ : parab K b)⁻¹ := rfl
  have e' : levi K b c ⟨x * h * x⁻¹, hm⟩ =
      leviHom b c ⟨x, hx⟩ * leviHom b c ⟨h, hh⟩ * (leviHom b c ⟨x, hx⟩)⁻¹ := by
    rw [e, ← map_inv, ← map_mul, ← map_mul]
    rfl
  beta_reduce
  rw [e', mul_assoc, FDRep.char_mul_comm, mul_assoc, inv_mul_cancel, mul_one]
  rfl

theorem hcChar : St.HCChar := by
  intro K _ _ _ ι _ _ s b lam
  exact ⟨character_hcRep b lam, isClassOn_hcFun b lam⟩

end GlobalTheory.CompanionTheory.FinGLChar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIsDPMorphismOfCompat
section
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatDP

theorem γB_map {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B']
    [Algebra ℚ B'] (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (g : B →+* B') {y : B}
    (hy : y ∈ Lat.IB f ξ) (hy' : g y ∈ Lat.IB f' ξ') (n : ℕ) :
    g ((Lat.γB f ξ).dpow n y) = (Lat.γB f' ξ').dpow n (g y) := by
  have h1 := (Lat.γB f ξ).factorial_mul_dpow_eq_pow (n := n) hy
  have h2 := (Lat.γB f' ξ').factorial_mul_dpow_eq_pow (n := n) hy'
  have hu : IsUnit (n.factorial : B') := by
    have := (IsUnit.mk0 (n.factorial : ℚ) (by exact_mod_cast n.factorial_ne_zero)).map (algebraMap ℚ B')
    rwa [map_natCast] at this
  apply hu.mul_left_cancel
  rw [h2, ← map_pow, ← h1, map_mul, map_natCast]

theorem isDPMorphism_map {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W']
    [CommRing B'] [Algebra ℚ B'] (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)
    (g : B →+* B') (hmap : ∀ x ∈ Lat.sub f ξ l M, g x ∈ Lat.sub f' ξ' l M) (u : W')
    (hg : g (f ξ) = f' (u * ξ')) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ))
    (hc' : Lat.DPClosed (Lat.ι f' ξ' l M) (Lat.γB f' ξ')) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γ f' ξ' l M hc') (Lat.map f ξ f' ξ' l M g hmap) := by
  have hB : ∀ x ∈ Lat.I f ξ l M, g (Lat.ι f ξ l M x) ∈ Lat.IB f' ξ' := by
    intro x hx
    have hx' : Lat.ι f ξ l M x ∈ Lat.IB f ξ := hx
    simp only [Lat.IB, Ideal.mem_span_singleton] at hx' ⊢
    obtain ⟨c, hc0⟩ := hx'
    refine ⟨f' u * g c, ?_⟩
    rw [hc0, map_mul, hg, map_mul]; ring
  have hI : ∀ x ∈ Lat.I f ξ l M, Lat.map f ξ f' ξ' l M g hmap x ∈ Lat.I f' ξ' l M := by
    intro x hx
    show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g hmap x) ∈ Lat.IB f' ξ'
    rw [Lat.ι_map]; exact hB x hx
  refine ⟨Ideal.map_le_iff_le_comap.2 fun x hx => hI x hx, fun {n} x hx => ?_⟩
  apply Lat.ι_injective f' ξ' l M
  rw [Lat.ι_γ f' ξ' l M hc' (hI x hx)]
  simp only [Lat.ι_map]
  rw [Lat.ι_γ f ξ l M hc hx]
  have hx' : Lat.ι f ξ l M x ∈ Lat.IB f ξ := hx
  exact (γB_map f ξ f' ξ' g hx' (hB x hx) n).symm

end GlobalTheory.CompanionTheory.LatDP
end

