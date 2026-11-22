import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftVectorZeroBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0128
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MrelConjTranspose
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

section rel

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def Rel (T : V →ₗ[ℂ] V') (A : Pr V) (A' : Pr V') : Prop :=
  A'.1 ∘ₗ T = T ∘ₗ A.1 ∧ A'.2.unop ∘ₗ T = T ∘ₗ A.2.unop

variable {T : V →ₗ[ℂ] V'}

private theorem rel_iff_forall_apply {A : Pr V} {A' : Pr V'} :
    Rel T A A' ↔ ∀ v, A'.1 (T v) = T (A.1 v) ∧ A'.2.unop (T v) = T (A.2.unop v) := by
  unfold Rel
  constructor
  · intro h v
    exact ⟨LinearMap.congr_fun h.1 v, LinearMap.congr_fun h.2 v⟩
  · intro h
    exact ⟨LinearMap.ext fun v => (h v).1, LinearMap.ext fun v => (h v).2⟩

theorem rel_mk {X : Module.End ℂ V} {Xs : Module.End ℂ V} {X' Xs' : Module.End ℂ V'}
    (h1 : ∀ v, X' (T v) = T (X v)) (h2 : ∀ v, Xs' (T v) = T (Xs v)) : Rel T (mkP X Xs) (mkP X' Xs') := by
  rw [rel_iff_forall_apply]
  intro v
  exact ⟨h1 v, h2 v⟩

theorem rel_add {A B : Pr V} {A' B' : Pr V'} (hA : Rel T A A') (hB : Rel T B B') : Rel T (A + B) (A' + B') := by
  rw [rel_iff_forall_apply] at *
  intro v
  constructor
  · show A'.1 (T v) + B'.1 (T v) = T (A.1 v + B.1 v)
    rw [map_add, (hA v).1, (hB v).1]
  · show A'.2.unop (T v) + B'.2.unop (T v) = T (A.2.unop v + B.2.unop v)
    rw [map_add, (hA v).2, (hB v).2]

theorem rel_neg {A : Pr V} {A' : Pr V'} (hA : Rel T A A') : Rel T (-A) (-A') := by
  rw [rel_iff_forall_apply] at *
  intro v
  constructor
  · show -A'.1 (T v) = T (-A.1 v)
    rw [map_neg, (hA v).1]
  · show -A'.2.unop (T v) = T (-A.2.unop v)
    rw [map_neg, (hA v).2]

theorem rel_zero : Rel T (0 : Pr V) (0 : Pr V') := by
  rw [rel_iff_forall_apply]
  intro v
  exact ⟨(map_zero T).symm, (map_zero T).symm⟩

theorem rel_mul {A B : Pr V} {A' B' : Pr V'} (hA : Rel T A A') (hB : Rel T B B') : Rel T (A * B) (A' * B') := by
  rw [rel_iff_forall_apply] at *
  intro v
  constructor
  · show A'.1 (B'.1 (T v)) = T (A.1 (B.1 v))
    rw [(hB v).1, (hA _).1]
  · show B'.2.unop (A'.2.unop (T v)) = T (B.2.unop (A.2.unop v))
    rw [(hA v).2, (hB _).2]

theorem rel_algebraMap (s : ℂ) : Rel T (algebraMap ℂ (Pr V) s) (algebraMap ℂ (Pr V') s) := by
  rw [rel_iff_forall_apply]
  intro v
  constructor
  · show (algebraMap ℂ (Module.End ℂ V') s) (T v) = T ((algebraMap ℂ (Module.End ℂ V) s) v)
    simp [Module.algebraMap_end_apply]
  · show (algebraMap ℂ (Module.End ℂ V') (conj s)) (T v) = T ((algebraMap ℂ (Module.End ℂ V) (conj s)) v)
    simp [Module.algebraMap_end_apply]

theorem rel_one : Rel T (1 : Pr V) (1 : Pr V') := by
  rw [rel_iff_forall_apply]
  intro v
  exact ⟨rfl, rfl⟩

theorem rel_smul (s : ℂ) {A : Pr V} {A' : Pr V'} (hA : Rel T A A') : Rel T (s • A) (s • A') := by
  rw [Algebra.smul_def, Algebra.smul_def]
  exact rel_mul (rel_algebraMap s) hA

theorem rel_star {A : Pr V} {A' : Pr V'} (hA : Rel T A A') : Rel T (star A) (star A') := by
  rw [rel_iff_forall_apply] at *
  intro v
  exact ⟨(hA v).2, (hA v).1⟩

theorem rel_sum {ι : Type*} (s : Finset ι) {A : ι → Pr V} {A' : ι → Pr V'} (h : ∀ i ∈ s, Rel T (A i) (A' i)) :
    Rel T (∑ i ∈ s, A i) (∑ i ∈ s, A' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rel_zero : Rel T (0 : Pr V) (0 : Pr V'))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact rel_add (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

def MRel (T : V →ₗ[ℂ] V') (M : Matrix (Fin 2) (Fin 2) (Pr V)) (M' : Matrix (Fin 2) (Fin 2) (Pr V')) : Prop :=
  ∀ a b, Rel T (M a b) (M' a b)

theorem mrel_mul {M N : Matrix (Fin 2) (Fin 2) (Pr V)} {M' N' : Matrix (Fin 2) (Fin 2) (Pr V')}
    (hM : MRel T M M') (hN : MRel T N N') : MRel T (M * N) (M' * N') := by
  intro a b
  simp only [Matrix.mul_apply]
  exact rel_sum _ (fun c _ => rel_mul (hM a c) (hN c b))

theorem mrel_conjTranspose {M : Matrix (Fin 2) (Fin 2) (Pr V)} {M' : Matrix (Fin 2) (Fin 2) (Pr V')}
    (hM : MRel T M M') : MRel T Mᴴ M'ᴴ := by
  intro a b
  exact rel_star (hM b a)

theorem mrel_one : MRel T (1 : Matrix (Fin 2) (Fin 2) (Pr V)) 1 := by
  intro a b
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact rel_one
  · exact rel_zero

theorem mrel_smul (s : ℂ) {M : Matrix (Fin 2) (Fin 2) (Pr V)} {M' : Matrix (Fin 2) (Fin 2) (Pr V')}
    (hM : MRel T M M') : MRel T (s • M) (s • M') := by
  intro a b
  exact rel_smul s (hM a b)

theorem mrel_Tm (Y : ℂ) {p c ci : Pr V} {p' c' ci' : Pr V'} (hp : Rel T p p') (hc : Rel T c c') (hci : Rel T ci ci') :
    MRel T (Formalism.YangianSpanCharacter.T.Tm Y p c ci) (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact rel_add (rel_algebraMap Y) hp
  · exact rel_neg hc
  · exact hci
  · exact rel_zero

end rel

section ops

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem t_tr {t : ℂ} (ht : t ≠ 0) (hz : inWb k ρ z) (hz' : inWb k ρ z')
    (X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))) (Y : ℂ) (a b : Fin 2)
    (Φ : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π') :
    Xs.t Y a b (trL ht z z' π π' Φ) = trL ht z z' π π' (X.t Y a b Φ) := by
  apply Subtype.ext
  funext c g
  by_cases hx : (c, g) ∈ DomR k ρ z z'
  · have hx' := (domR_iota ht z z' c g).2 hx
    rw [Xs.t_apply Y a b _ (c, g) hx, trL_apply]
    show _ = (X.t Y a b Φ).1 (consC t c) (ιLev k 1 ρ g)
    rw [X.t_apply Y a b Φ _ hx']
    exact (tL_iota (E := Wq →L[ℂ] Wp) hz hz' Y a b ((Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)) (consC t c)) hx.2.1).symm
  · rw [(Xs.t Y a b (trL ht z z' π π' Φ)).2.1 (c, g) hx, trL_apply]
    exact ((X.t Y a b Φ).2.1 _ (fun h => hx ((domR_iota ht z z' c g).1 h))).symm

theorem op_tr {t : ℂ} (ht : t ≠ 0)
    (X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))) (l : Fin ρ) (i : Fin 6)
    (Φ : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π') :
    Xs.op l i (trL ht z z' π π' Φ) = trL ht z z' π π' (X.op (shS l) i Φ) := by
  apply Subtype.ext
  rw [Xs.op_apply, trL_apply, trL_apply, X.op_apply]
  funext c g
  exact opL_consC ht (fun c' => (Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)) c' (ιLev k 1 ρ g)) c
    (fun h => diff_rad Φ.2 _ h) l i

end ops

section chain

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem site_rel {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (l : Fin ρ) (Y : ℂ) :
    MRel (trL ht z z' π π') (Wd.Ts (P5.site L (shS l)) Y) (Wd.Ts (P5.site Ls l) Y) := by
  have hop := fun (i : Fin 6) Φ => op_tr ht X Xs l i Φ
  refine mrel_Tm Y ?_ ?_ ?_
  · show Rel _ (L.p (shS l)) (Ls.p l)
    rw [hL.1, hLs.1]
    exact rel_mk (fun v => hop 0 v) (fun v => by simp only [LinearMap.neg_apply, hop 3, map_neg])
  · show Rel _ (L.c (shS l)) (Ls.c l)
    rw [hL.2.2.1, hLs.2.2.1]
    exact rel_mk (fun v => hop 1 v) (fun v => hop 4 v)
  · show Rel _ (L.ci (shS l)) (Ls.ci l)
    rw [hL.2.2.2.1, hLs.2.2.2.1]
    exact rel_mk (fun v => hop 2 v) (fun v => hop 5 v)

theorem tprod_rel {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (Y : ℂ) :
    ∀ m n : ℕ, ρ - n = m → MRel (trL ht z z' π π') (P5.tprod L Y (n + 1)) (P5.tprod Ls Y n) := by
  intro m
  induction m with
  | zero =>
    intro n hn
    have e1 : P5.tprod L Y (n + 1) = 1 := by rw [P5.tprod, dif_neg (by omega)]
    have e2 : P5.tprod Ls Y n = 1 := by rw [P5.tprod, dif_neg (by omega)]
    rw [e1, e2]
    exact mrel_one
  | succ m ih =>
    intro n hn
    have e1 : P5.tprod L Y (n + 1) = P5.tprod L Y (n + 1 + 1) * Wd.Ts (P5.site L ⟨n + 1, by omega⟩) Y := by
      rw [P5.tprod, dif_pos (by omega)]
    have e2 : P5.tprod Ls Y n = P5.tprod Ls Y (n + 1) * Wd.Ts (P5.site Ls ⟨n, by omega⟩) Y := by
      rw [P5.tprod, dif_pos (by omega)]
    rw [e1, e2]
    refine mrel_mul (ih (n + 1) (by omega)) ?_
    have e : (⟨n + 1, by omega⟩ : Fin (1 + ρ)) = shS ⟨n, by omega⟩ := rfl
    rw [e]
    exact site_rel ht hL hLs _ Y

theorem qqi_rel {t : ℂ} (ht : t ≠ 0) (hz : inWb k ρ z) (hz' : inWb k ρ z')
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {st : Fr.Start (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'))}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    {sts : Fr.Start (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))))} {s : ℂ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y) (Y : ℂ) :
    MRel (trL ht z z' π π') (P5.QQi L st 1 Y) (P5.QQi Ls sts 0 Y) := by
  have hQ : MRel (trL ht z z' π π') (st.QQ Y) (sts.QQ Y) := by
    rw [hst, hsts]
    refine mrel_smul s fun a b => rel_mk (fun v => t_tr ht hz hz' X Xs Y a b v) (fun v => t_tr ht hz hz' X Xs _ b a v)
  unfold P5.QQi
  have h1 : ((1 : Fin (1 + ρ + 1)) : ℕ) = 0 + 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have h0 : ((0 : Fin (ρ + 1)) : ℕ) = 0 := rfl
  rw [h1, h0]
  exact mrel_mul (mrel_mul (mrel_conjTranspose (tprod_rel ht hL hLs _ _ 0 rfl)) hQ) (tprod_rel ht hL hLs _ _ 0 rfl)

end chain

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PairOperatorCommute
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Abstract

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ}

theorem fn_comm6 (L : R.LevelData A r) {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : x * y = y * x := L.fns_comm x hx y hy

theorem c_fns (L : R.LevelData A r) (l : Fin r) : L.c l ∈ L.fns := by
  exact Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))
theorem ci_fns (L : R.LevelData A r) (l : Fin r) : L.ci l ∈ L.fns := by
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))
theorem cb_fns (L : R.LevelData A r) (l : Fin r) : L.cb l ∈ L.fns := by
  exact Or.inl (Or.inl (Or.inr ⟨l, rfl⟩))
theorem cbi_fns (L : R.LevelData A r) (l : Fin r) : L.cbi l ∈ L.fns := by
  exact Or.inl (Or.inr ⟨l, rfl⟩)

theorem hol_comm_star (L : R.LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) (l m : Fin r) :
    ∀ x ∈ hol (⟨L.p l, L.c l, L.ci l⟩ : Site A), ∀ y ∈ hol (⟨L.p m, L.c m, L.ci m⟩ : Site A), Commute x (star y) := by
  have hf : ∀ x ∈ L.fns, ∀ y ∈ L.fns, Commute x y := fun x hx y hy => L.fns_comm x hx y hy
  intro x hx y hy
  simp only [hol, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hy with rfl | rfl | rfl
  · rw [hp]
    refine Commute.neg_right ?_
    rcases hx with rfl | rfl | rfl
    · exact L.p_pb l m
    · exact (L.pb_c m l).symm
    · exact (L.pb_ci m l).symm
  · rw [hc]
    rcases hx with rfl | rfl | rfl
    · exact L.p_cb l m
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩)))
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩)))
  · rw [hci]
    rcases hx with rfl | rfl | rfl
    · exact L.p_cbi l m
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inr ⟨m, rfl⟩))
    · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inr ⟨m, rfl⟩))

theorem hol_comm_hol (L : R.LevelData A r) {l m : Fin r} (hlm : l ≠ m) :
    ∀ x ∈ hol (⟨L.p l, L.c l, L.ci l⟩ : Site A), ∀ y ∈ hol (⟨L.p m, L.c m, L.ci m⟩ : Site A), Commute x y := by
  have hf : ∀ x ∈ L.fns, ∀ y ∈ L.fns, Commute x y := fun x hx y hy => L.fns_comm x hx y hy
  have hlm' : m ≠ l := fun h => hlm h.symm
  intro x hx y hy
  simp only [hol, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact L.p_p l m
  · have := L.p_c l m; rw [if_neg hlm, add_zero] at this; exact this
  · have := L.p_ci l m; rw [if_neg hlm, sub_zero] at this; exact this
  · have := L.p_c m l; rw [if_neg hlm', add_zero] at this; exact this.symm
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨m, rfl⟩))))
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩))))
  · have := L.p_ci m l; rw [if_neg hlm', sub_zero] at this; exact this.symm
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨m, rfl⟩))))
  · exact hf _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))) _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨m, rfl⟩))))

theorem good_of_adm {S : Type} (st : Fr.Start A) (w : List (Letter ℂ S)) (hw : Fr.admitted st w) : Good w := by
  obtain ⟨h1, h2, -, h4⟩ := hw
  refine ⟨h1, h2, h4.imp fun {l l'} h => ?_⟩
  unfold RegL
  split_ifs
  · simpa using h 1 (by norm_num)
  · intro h'
    apply h (-1) (by norm_num)
    push_cast
    linear_combination -h'

end Abstract

section Pairs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pair_operator_commute {a b c d : Module.End ℂ V} (h1 : a * c = c * a) (h2 : d * b = b * d) :
    (mkP a b : Pr V) * mkP c d = mkP c d * mkP a b := by
  refine Prod.ext ?_ ?_
  · show a * c = c * a
    exact h1
  · show MulOpposite.op b * MulOpposite.op d = MulOpposite.op d * MulOpposite.op b
    rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, h2]

end Pairs

section Levels

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem star_site_ops {X : ActualOps k r z z' π π'} {L : R.LevelData (Pr (RadSp k r z z' π π')) r}
    (hL : IsActualLevel X L) :
    (∀ l, star (L.p l) = -L.pb l) ∧ (∀ l, star (L.c l) = L.cb l) ∧ ∀ l, star (L.ci l) = L.cbi l := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  have hs : ∀ a b : Module.End ℂ (RadSp k r z z' π π'), star (mkP a b : Pr (RadSp k r z z' π π')) = mkP b a :=
    fun a b => rfl
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_⟩
  · rw [hp, hpb, hs]
    refine Prod.ext rfl ?_
    show MulOpposite.op (X.op l 0) = -MulOpposite.op (-X.op l 0)
    rw [← MulOpposite.op_neg, neg_neg]
  · rw [hc, hcb, hs]
  · rw [hci, hcbi, hs]

theorem isSite_actual {X : ActualOps k r z z' π π'} {L : R.LevelData (Pr (RadSp k r z z' π π')) r}
    (hL : IsActualLevel X L) (l : Fin r) : IsSite (site L l) := by
  obtain ⟨hp, hc, hci⟩ := star_site_ops hL
  refine ⟨⟨L.c_ci l, L.ci_c l, ?_⟩, hol_comm_star L hp hc hci l l⟩
  have h := L.p_c l l
  rw [if_pos rfl] at h
  exact h

theorem QQi_mem_all (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))) (i : Fin (r + 1)) (Y : ℂ)
    (hQ : ∀ a b, st.QQ Y a b ∈ 𝒜)
    (hS : ∀ l : Fin r, i.val ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) (a b : Fin 2) :
    QQi L st i Y a b ∈ 𝒜 := by
  have hmul : ∀ M N : M2 (Pr (RadSp k r z z' π π')), (∀ a b, M a b ∈ 𝒜) → (∀ a b, N a b ∈ 𝒜) →
      ∀ a b, (M * N) a b ∈ 𝒜 := by
    intro M N hM hN a b
    rw [Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun c _ => Subalgebra.mul_mem _ (hM a c) (hN c b)
  have hone : ∀ a b, (1 : M2 (Pr (RadSp k r z z' π π'))) a b ∈ 𝒜 := by
    intro a b
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hct : ∀ M : M2 (Pr (RadSp k r z z' π π')), (∀ a b, M a b ∈ 𝒜) → ∀ a b, Mᴴ a b ∈ 𝒜 := by
    intro M hM a b
    rw [Matrix.conjTranspose_apply]
    exact star_mem (hM b a)
  have hts : ∀ (Y' : ℂ) (l : Fin r), i.val ≤ l.val → ∀ a b, Ts (site L l) Y' a b ∈ 𝒜 := by
    intro Y' l hl a b
    obtain ⟨hp, hc, hci⟩ := hS l hl
    fin_cases a <;> fin_cases b
    · exact add_mem (algebraMap_mem 𝒜 Y') hp
    · exact neg_mem hc
    · exact hci
    · exact zero_mem _
  have htp : ∀ (Y' : ℂ) (n j : ℕ), r - j = n → i.val ≤ j → ∀ a b, tprod L Y' j a b ∈ 𝒜 := by
    intro Y' n
    induction n with
    | zero =>
      intro j hj hij
      rw [tprod, dif_neg (by omega)]
      exact hone
    | succ n ih =>
      intro j hj hij
      rw [tprod, dif_pos (by omega)]
      exact hmul _ _ (ih (j + 1) (by omega) (by omega)) (hts Y' ⟨j, by omega⟩ hij)
  unfold QQi
  exact hmul _ _ (hmul _ _ (hct _ (htp _ _ _ rfl le_rfl)) hQ) (htp _ _ _ rfl le_rfl) a b

theorem QQi_castSucc (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (l : Fin r) (Y : ℂ) (hY : star Y = Y) :
    QQi L st l.castSucc Y = (Ts (site L l) Y)ᴴ * QQi L st l.succ Y * Ts (site L l) Y := by
  have ht : ∀ Y' : ℂ, tprod L Y' (l.castSucc : ℕ) = tprod L Y' (l.succ : ℕ) * Ts (site L l) Y' := by
    intro Y'
    rw [tprod, dif_pos (show (l.castSucc : ℕ) < r from l.isLt)]
    rfl
  unfold QQi
  rw [ht, ht, hY, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end Levels

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem qqCommutes_actual (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (l : Fin P.r) : QQCommutes (QQi L st l.succ) (site L l) := by
  obtain ⟨hpl, -, hL, hQQ, -⟩ := hD
  obtain ⟨sp, sc, sci⟩ := star_site_ops hL
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have ht : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * X.op l i = X.op l i * X.t Y a b :=
    fun i => (Formalism.FourierDecayAlt.P.level_coordinates_commute Wp Wq P z z' π π' hpl X l i).1
  have htn : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * -X.op l i = -X.op l i * X.t Y a b := by
    intro i Y a b; rw [mul_neg, neg_mul, ht]
  intro Y
  have hmem : ∀ a b, QQi L st l.succ Y a b ∈ StarSubalgebra.centralizer ℂ (hol (site L l)) := by
    refine QQi_mem_all L st _ l.succ Y ?_ ?_
    · intro a b
      rw [hQQ Y, Matrix.smul_apply]
      refine SMulMemClass.smul_mem _ ?_
      simp only [ActualOps.QQ, Matrix.of_apply]
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      simp only [hol, site, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · rw [hp l]
        exact ⟨pair_operator_commute (ht _ _ _ _).symm (htn _ _ _ _), pair_operator_commute (htn _ _ _ _).symm (ht _ _ _ _)⟩
      · rw [hc l]
        exact ⟨pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
      · rw [hci l]
        exact ⟨pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
    · intro m hm
      have hne : l ≠ m := by
        intro h; rw [← h, Fin.val_succ] at hm; omega
      have key : ∀ y ∈ hol (site L m), y ∈ StarSubalgebra.centralizer ℂ (hol (site L l)) := by
        intro y hy
        rw [StarSubalgebra.mem_centralizer_iff]
        intro g hg
        exact ⟨hol_comm_hol L hne g hg y hy, (hol_comm_star L sp sc sci m l y hy g hg).symm⟩
      exact ⟨key _ (by simp [hol, site]), key _ (by simp [hol, site]), key _ (by simp [hol, site])⟩
  intro a b x hx
  have h := hmem a b
  rw [StarSubalgebra.mem_centralizer_iff] at h
  rcases hx with hx | hx
  · exact (h x hx).1.symm
  · have h2 := (h _ hx).2
    rw [star_star] at h2
    exact h2.symm

theorem siteStep_actual (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (w : List (Letter ℂ S)) (hD : IsData P z z' π π' X μ L st l0) (hw : WordOK P z z' π π' st l0 w) (l : Fin P.r) :
    star (bTl L l w) * RRi L st l.succ w * bTl L l w = RRi L st l.castSucc w := (by
    have hL := hD.2.2.1
    exact Formalism.FourierDecayAlt.P.site_exchange_relation ℂ _ S (site L l) (QQi L st l.succ) (QQi L st l.castSucc) w
      (isSite_actual hL l) (qqCommutes_actual P z z' π π' X μ L st l0 hD l)
      (fun Y hY => QQi_castSucc L st l Y hY) (good_of_adm st w hw.1))

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

