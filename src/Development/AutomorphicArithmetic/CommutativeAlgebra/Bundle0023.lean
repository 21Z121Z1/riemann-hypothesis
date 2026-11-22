import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0018

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

private theorem sec_empty {R : Type} [CommRing R] (F : Shv R) (T : Scheme.{0}) [IsEmpty T] (a : Sec F T) : a = 0 :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue R F T).1 a 0 ⟨⊥, Scheme.bot_mem_grothendieckTopology T, fun _ _ h => h.elim⟩

private theorem free_sec_zero (R : Type) [CommRing R] (P : PSh)
    (hP : ∀ T : Scheme.{0}, Nonempty (P.obj (op T)) → IsEmpty T) (U : Scheme.{0})
    (y : Sec ((free R).obj P) U) : y = 0 := by
  obtain ⟨S, hS, h⟩ := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R P U).1 y
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue R _ U).1 y 0 ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨c, hc⟩ := h V g hg
  have h0 : Sec.res g (0 : Sec ((free R).obj P) U) = 0 := map_zero (((free R).obj P).obj.map g.op).hom
  rw [h0]
  by_cases hV : IsEmpty V
  · exact sec_empty _ _ _
  · rw [hc]
    have : IsEmpty (P.obj (op V)) := ⟨fun x => hV (hP V ⟨x⟩)⟩
    have hc0 : c = 0 := Subsingleton.elim _ _
    simp [hc0]

private theorem free_isZero (R : Type) [CommRing R] (P : PSh)
    (hP : ∀ T : Scheme.{0}, Nonempty (P.obj (op T)) → IsEmpty T) : IsZero ((free R).obj P) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  ext U y
  exact free_sec_zero R P hP U.unop y

private theorem sx_empty (E : Spc) (p : ℕ) (T : Scheme.{0})
    (x : Sx (pullback (triv E 0) (PGL.pr 0)) p T) : IsEmpty T := by
  have y : Sx (PGL 0) p T := Sx.map (pullback.snd (triv E 0) (PGL.pr 0)) x
  have v : Um 0 Γ(T, ⊤) := (show ComposableArrows (Um 0 Γ(T, ⊤)) p from y).obj 0
  have h : (⊥ : Ideal Γ(T, ⊤)) = ⊤ := by
    have := v.2
    rwa [Set.range_eq_empty, Ideal.span_empty] at this
  have hs : Subsingleton Γ(T, ⊤) := by
    rcases subsingleton_or_nontrivial Γ(T, ⊤) with hs | hn
    · exact hs
    · exact absurd h bot_ne_top
  refine ⟨fun t => ?_⟩
  have := (T.presheaf.germ ⊤ t trivial).hom.codomain_trivial
  exact not_subsingleton (T.presheaf.stalk t) this

private theorem chains_isZero (R : Type) [CommRing R] (X : Spc)
    (hX : ∀ (p : ℕ) (T : Scheme.{0}), Nonempty (Sx X p T) → IsEmpty T) (k : ℤ) :
    IsZero (((chains R).obj X).X k) := by
  by_cases hk : k ≤ 0
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, k = -(p : ℤ) := ⟨(-k).toNat, by omega⟩
    exact (free_isZero R _ (hX p)).of_iso (chainsXIso R X p)
  · refine HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingDownNat k fun i => ?_
    change -(i : ℤ) ≠ k
    omega

private theorem H_subsingleton (R : Type) [CommRing R] (X : Spc)
    (hX : ∀ (p : ℕ) (T : Scheme.{0}), Nonempty (Sx X p T) → IsEmpty T) (F : Shv R) (n : ℤ) :
    Subsingleton (H R X F n) := ⟨fun a b => by
  obtain ⟨a, rfl⟩ := a.mk_surjective
  obtain ⟨b, rfl⟩ := b.mk_surjective
  congr 1
  exact Cocycle.ext (Cochain.ext _ _ fun p q h => (chains_isZero R X hX p).eq_of_src _ _)⟩

theorem UpperTheory.projectiveBundleFormula_rank_zero :
    ∀ (q : ℕ) [NeZero q] (E : Spc), PBF q E 0 := by
  intro q _ E n i
  haveI : Subsingleton (Ht q (pullback (triv E 0) (PGL.pr 0)) n i) :=
    H_subsingleton _ _ (fun p T ⟨x⟩ => sx_empty E p T x) _ _
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨fun j => j.elim0, Subsingleton.elim _ _⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexIsAdmissible
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem sx_face_face {E : Spc} {p : ℕ} {U : Scheme} (y : Sx E (p+2) U) {a b : Fin (p+2)}
    (h : a ≤ b) : (y.face b.succ).face a = (y.face a.castSucc).face b := by
  unfold Sx.face
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← NatTrans.comp_app,
    SimplicialObject.δ_comp_δ E h]

private theorem sum_neg_one_pow_face_face_eq_zero {A : Type*} [AddCommGroup A] {E : Spc} {p : ℕ} {U : Scheme}
    (f : Sx E p U → A) (y : Sx E (p+2) U) :
    ∑ j : Fin (p+3), ∑ i : Fin (p+2), ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) • f ((y.face j).face i) = 0 := by
  have ff : ∀ {a b : Fin (p+2)}, a ≤ b → (y.face b.succ).face a = (y.face a.castSucc).face b :=
    fun h => sx_face_face y h
  rw [← Finset.sum_product' (f := fun (j : Fin (p+3)) (i : Fin (p+2)) => ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) • f ((y.face j).face i)), Finset.univ_product_univ]
  let g : Fin (p+3) × Fin (p+2) → Fin (p+3) × Fin (p+2) := fun ji =>
    if h : (ji.1 : ℕ) ≤ ji.2 then (ji.2.succ, ji.1.castLT (by omega))
    else (ji.2.castSucc, ji.1.pred (by intro h0; simp [h0] at h))
  have gg : ∀ ji, g (g ji) = ji := by
    rintro ⟨j, i⟩
    by_cases h : (j : ℕ) ≤ i
    · have h1 : ¬ ((i.succ : Fin (p+3)) : ℕ) ≤ (j.castLT (by omega) : Fin (p+2)) := by simp; omega
      simp only [g, dif_pos h, dif_neg h1]
      ext <;> simp
    · have h1 : ((i.castSucc : Fin (p+3)) : ℕ) ≤ (j.pred (by intro h0; simp [h0] at h) : Fin (p+2)) := by simp; omega
      simp only [g, dif_neg h, dif_pos h1]
      ext <;> simp
  refine Finset.sum_involution (fun ji _ => g ji) ?_ ?_ (fun _ _ => Finset.mem_univ _) (fun ji _ => gg ji)
  · rintro ⟨j, i⟩ _
    by_cases h : (j : ℕ) ≤ i
    · simp only [g, dif_pos h]
      have hj : j = (j.castLT (by omega) : Fin (p+2)).castSucc := by ext; simp
      have hle : j.castLT (by omega) ≤ i := by rw [Fin.le_def]; simpa using h
      rw [ff hle, ← hj]
      simp only [Fin.val_succ, Fin.coe_castLT]
      rw [← add_smul]
      convert zero_smul ℤ _
      rw [show (i : ℕ) + 1 + j = (j + i) + 1 by ring, pow_succ]; ring
    · simp only [g, dif_neg h]
      have hj0 : j ≠ 0 := by intro h0; simp [h0] at h
      have hle : i ≤ j.pred hj0 := by rw [Fin.le_def]; simp; omega
      have key : (y.face j).face i = (y.face i.castSucc).face (j.pred hj0) := by
        have := ff hle
        rwa [Fin.succ_pred] at this
      rw [key]
      simp only [Fin.coe_castSucc, Fin.coe_pred]
      rw [← add_smul]
      convert zero_smul ℤ _
      have : (j : ℕ) = (j : ℕ) - 1 + 1 := by omega
      rw [this, show (j : ℕ) - 1 + 1 - 1 = (j:ℕ) - 1 by omega, show (j:ℕ) - 1 + 1 + i = (i + (j - 1)) + 1 by ring, pow_succ]; ring
  · rintro ⟨j, i⟩ _ _ heq
    by_cases h : (j : ℕ) ≤ i
    · simp only [g, dif_pos h, Prod.mk.injEq] at heq
      have := congrArg Fin.val heq.1; simp at this; omega
    · simp only [g, dif_neg h, Prod.mk.injEq] at heq
      have := congrArg Fin.val heq.1; simp at this; omega

theorem UpperTheory.supportDoubleComplex_isAdmissible :
    ∀ (R : Type) [CommRing R] (E : Spc) (Z : Sub E) (K : Cx R) (m : ℤ), (famDC Z K m).Ok := by
  intro R _ E Z K m
  unfold famDC
  constructor
  · intro p s t u x
    apply Subtype.ext
    funext U y
    change Sec.map (K.d (s + m) (t + m) ≫ K.d (t + m) (u + m)) (x.1 U y) = 0
    rw [HomologicalComplex.d_comp_d]
    rfl
  · intro p s x
    apply Subtype.ext
    funext U y
    simp [Fam.δ]
    have hz := sum_neg_one_pow_face_face_eq_zero (fun z => (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U z) y
    have hj : ∀ j : Fin (p+3), (-1 : ℤ) ^ (j : ℕ) • m.negOnePow • ∑ i : Fin (p+2), (-1 : ℤ) ^ (i : ℕ) •
        (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U ((y.face j).face i) =
        m.negOnePow • ∑ i : Fin (p+2), ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) •
        (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U ((y.face j).face i) := by
      intro j
      rw [smul_comm, Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, pow_add]
    simp_rw [hj, ← Finset.smul_sum]
    rw [hz, smul_zero, smul_zero]
  · intro p s t x
    apply Subtype.ext
    funext U y
    simp [Fam.map, Fam.δ]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexTotalRepresentsVanishingCoch
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem map_res' {E E' : Spc} (j : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (z : Sx E p U) :
    (z.map j).res g = (z.res g).map j := by
  exact (FunctorToTypes.naturality (j.app _) g.op z).symm

private theorem map_face' {E E' : Spc} (j : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (z : Sx E (p + 1) U) (i : Fin (p + 2)) :
    (z.map j).face i = (z.face i).map j :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (j.naturality (SimplexCategory.δ i).op) (op U)) z).symm

private theorem ev_delta_zero {R : Type} [CommRing R] {E : Spc} {I : Cx R} {N M s t : ℤ} (hm : N + 1 = M)
    (α : Cochain ((chains R).obj E) I N) (U : Scheme.{0}) (x : Sx E 0 U)
    (ht : -((0 : ℕ) : ℤ) + M = t) (hs : -((0 : ℕ) : ℤ) + N = s) :
    ev (δ N M α) 0 t ht U x = Sec.map (I.d s t) (ev α 0 s hs U x) := by
  obtain rfl : t = M := by omega
  obtain rfl : s = N := by omega
  exact (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R hm α U).1 x

private theorem fam_smul_apply {R : Type} [CommRing R] {E : Spc} {Z : Sub E} {p : ℕ} {M : Shv R} (u : ℤˣ) (a : Fam Z p M)
    (U : Scheme.{0}) (z : Sx E p U) : (u • a).1 U z = u • a.1 U z := by
  rfl

theorem UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain :
    ∀ (R : Type) [CommRing R] {E E' : Spc} (j : E ⟶ E') (Z : Sub E) (K : Cx R) (m n N : ℤ), n + m = N →
    (∀ γ : Cochain ((chains R).obj E') K N, (∀ (p : ℕ) (s : ℤ) h (U : Scheme.{0}) (z : Sx E p U), Z.mem p U z → ev γ p s h U (z.map j) = 0) → ∃ x : (famDC Z K m).Tot, (famDC Z K m).Deg n x ∧ Comp j γ x) ∧
    (∀ (γ : Cochain ((chains R).obj E') K N) (x x' : (famDC Z K m).Tot), (famDC Z K m).Deg n x → (famDC Z K m).Deg n x' → Comp j γ x → Comp j γ x' → x = x') ∧
    (∀ (γ : Cochain ((chains R).obj E') K N) (x : (famDC Z K m).Tot), Comp j γ x → Comp j (δ N (N + 1) γ) ((famDC Z K m).D n x)) ∧
    (∀ (γ γ' : Cochain ((chains R).obj E') K N) (x x' : (famDC Z K m).Tot), Comp j γ x → Comp j γ' x' → Comp j (γ - γ') (x - x')) ∧
    ∀ x : (famDC Z K m).Tot, (famDC Z K m).Deg n x → (famDC Z K m).Deg (n + 1) ((famDC Z K m).D n x) := by
  intro R _ E E' j Z K m n N hN
  have ev_nat := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E') (I := K) (n := N)).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    let x : (famDC Z K m).Tot := fun p s =>
      if h : -(p : ℤ) + N = s + m then
        (⟨fun U z => ev γ p (s + m) h U (z.map j),
          ⟨fun V U g z => (ev_nat γ p (s + m) h V U g (z.map j)).trans (by rw [map_res']),
           fun U z hz => hγ p (s + m) h U z hz⟩⟩ : Fam Z p (K.X (s + m)))
      else 0
    refine ⟨x, fun p s hps => ?_, fun p s h U z => ?_⟩
    · have h : ¬ (-(p : ℤ) + N = s + m) := by omega
      exact dif_neg h
    · exact congrArg (fun a : Fam Z p (K.X (s + m)) =>
        (a : (U : Scheme.{0}) → Sx E p U → Sec (K.X (s + m)) U) U z) (dif_pos h)
  · intro γ x x' hx hx' cx cx'
    funext p s
    by_cases hps : (p : ℤ) + s = n
    · have h : -(p : ℤ) + N = s + m := by omega
      change (x p s : Fam Z p (K.X (s + m))) = x' p s
      apply Subtype.ext
      funext U z
      exact (cx p s h U z).trans (cx' p s h U z).symm
    · rw [hx p s hps, hx' p s hps]
  · intro γ x cx p s h U z
    rcases p with _ | p
    · have h0 : -((0 : ℕ) : ℤ) + N = (s - 1) + m := by omega
      rw [ev_delta_zero (s := s - 1 + m) rfl γ U (z.map j) h h0, ← cx 0 (s - 1) h0 U z]
      rfl
    · have hs : -((p + 1 : ℕ) : ℤ) + N = (s - 1) + m := by omega
      have hp : -(p : ℤ) + N = s + m := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R (rfl : N + 1 = N + 1) γ U).2 p (s - 1 + m) (s + m) hs h (z.map j),
        ← cx (p + 1) (s - 1) hs U z]
      simp only [map_face']
      rw [Finset.sum_congr rfl (fun i _ => by rw [← cx p s hp U (z.face i)])]
      have eN : (N + 1).negOnePow = (n + 1).negOnePow * m.negOnePow := by
        rw [← Int.negOnePow_add]; congr 1; omega
      have e2 := fam_smul_apply (n + 1).negOnePow
        (Fam.δ Z p (K.X (s + m)) m.negOnePow (x p s : Fam Z p (K.X (s + m)))) U z
      rw [eN, mul_smul]
      show Sec.map (K.d (s - 1 + m) (s + m)) ((x (p + 1) (s - 1) : Fam Z (p + 1) (K.X (s - 1 + m))).1 U z) +
        ((n + 1).negOnePow • Fam.δ Z p (K.X (s + m)) m.negOnePow (x p s : Fam Z p (K.X (s + m)))).1 U z = _
      rw [e2]
      rfl
  · intro γ γ' x x' cx cx' p s h U z
    rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E') (I := K) (n := N)).1 γ γ' p (s + m) h U (z.map j)).2.1,
      ← cx p s h U z, ← cx' p s h U z]
    rfl
  · intro x hx p s hps
    rcases p with _ | p
    · have h1 : ((0 : ℕ) : ℤ) + (s - 1) ≠ n := by omega
      show (Fam.map Z 0 (K.d (s - 1 + m) (s + m))) (x 0 (s - 1)) = 0
      rw [hx 0 (s - 1) h1]
      exact map_zero _
    · have h1 : ((p + 1 : ℕ) : ℤ) + (s - 1) ≠ n := by omega
      have h2 : (p : ℤ) + s ≠ n := by omega
      show (Fam.map Z (p + 1) (K.d (s - 1 + m) (s + m))) (x (p + 1) (s - 1)) +
        (n + 1).negOnePow • (Fam.δ Z p (K.X (s + m)) m.negOnePow) (x p s) = 0
      rw [hx _ _ h1, hx _ _ h2]
      show (Fam.map Z (p + 1) (K.d (s - 1 + m) (s + m))) (0 : Fam Z (p + 1) (K.X (s - 1 + m))) +
        (n + 1).negOnePow • (Fam.δ Z p (K.X (s + m)) m.negOnePow) (0 : Fam Z p (K.X (s + m))) = 0
      rw [map_zero, map_zero, smul_zero, add_zero]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TotalExactOfColumnExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem map_us {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (e : ℤˣ) (x : G) :
    f (e • x) = e • f x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

private theorem D_zero (C : DC) (n : ℤ) (x : C.Tot) (s t : ℤ) (h : s + 1 = t) :
    C.D n x 0 t = C.d 0 s t (x 0 s) := by
  obtain rfl : s = t - 1 := by omega
  rfl

private theorem D_succ (C : DC) (n : ℤ) (x : C.Tot) (p : ℕ) (s t : ℤ) (h : s + 1 = t) :
    C.D n x (p + 1) t = C.d (p + 1) s t (x (p + 1) s) + (n + 1).negOnePow • C.δ p t (x p t) := by
  obtain rfl : s = t - 1 := by omega
  rfl

private theorem col {C C' : DC} {Φ : C.Hom C'} {p : ℕ} (h : Φ.ColEx p) (r s t u : ℤ) (e1 : r + 1 = s)
    (e2 : s + 1 = t) (e3 : t + 1 = u) (a : C.A p t) (y : C'.A p s) (ha : C.d p t u a = 0)
    (hy : Φ p t a = C'.d p s t y) :
    ∃ (a' : C.A p s) (y' : C'.A p r), C.d p s t a' = a ∧ y = Φ p s a' + C'.d p r s y' := by
  subst e2
  subst e3
  obtain rfl : r = s - 1 := by omega
  exact h s a y ha hy

private structure Cl {C C' : DC} (Φ : C.Hom C') (n : ℤ) (p : ℕ) (b : ∀ s, C.A p s) (z : ∀ s, C'.A p s) : Prop where
  sb : ∀ s, (p : ℤ) + s ≠ n + 1 → b s = 0
  sz : ∀ s, (p : ℤ) + s ≠ n → z s = 0
  db : ∀ s t, s + 1 = t → C.d p s t (b s) = 0
  pz : ∀ s t, s + 1 = t → Φ p t (b t) = C'.d p s t (z s)

private structure Sv {C C' : DC} (Φ : C.Hom C') (n : ℤ) (p : ℕ) (b : ∀ s, C.A p s) (z : ∀ s, C'.A p s)
    (u : ∀ s, C.A p s) (v : ∀ s, C'.A p s) : Prop where
  su : ∀ s, (p : ℤ) + s ≠ n → u s = 0
  sv : ∀ s, (p : ℤ) + s ≠ n - 1 → v s = 0
  du : ∀ s t, s + 1 = t → C.d p s t (u s) = b t
  yv : ∀ r s, r + 1 = s → z s = Φ p s (u s) + C'.d p r s (v r)

private theorem solve {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {p : ℕ} (hcol : Φ.ColEx p)
    {b : ∀ s, C.A p s} {z : ∀ s, C'.A p s} (h : Cl Φ n p b z) : ∃ u v, Sv Φ n p b z u v := by
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℤ, s0 = n - p := ⟨_, rfl⟩
  obtain ⟨a', y', ha', hy'⟩ := col hcol (s0 - 1) s0 (s0 + 1) (s0 + 1 + 1) (by ring) rfl rfl
    (b (s0 + 1)) (z s0) (h.db _ _ rfl) (h.pz _ _ rfl)
  refine ⟨Function.update (fun _ => 0) s0 a', Function.update (fun _ => 0) (s0 - 1) y',
    ⟨?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    rw [Function.update_of_ne (by omega)]
  · intro s hs
    rw [Function.update_of_ne (by omega)]
  · intro s t hst
    by_cases hs : s = s0
    · subst hst
      subst hs
      rw [Function.update_self, ha']
    · simp [Function.update_of_ne hs, h.sb t (by omega)]
  · intro r s hrs
    by_cases hs : s = s0
    · have hr : r = s - 1 := by omega
      subst hr
      subst hs
      rw [Function.update_self, Function.update_self, hy']
    · have hr : r ≠ s0 - 1 := by omega
      simp [Function.update_of_ne hs, Function.update_of_ne hr, h.sz s (by omega)]

private structure St {C C' : DC} (Φ : C.Hom C') (n : ℤ) (a : C.Tot) (y : C'.Tot) (p : ℕ) where
  b : ∀ s, C.A p s
  z : ∀ s, C'.A p s
  u : ∀ s, C.A p s
  v : ∀ s, C'.A p s
  cl : Cl Φ n p b z
  sv : Sv Φ n p b z u v
  hb : ∀ s, C.δ p s (a p s) = C.δ p s (b s)
  hz : ∀ s, C'.δ p s (y p s) = C'.δ p s (z s)

private theorem cl_zero {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {a : C.Tot} {y : C'.Tot}
    (ha : C.Deg (n + 1) a) (hy : C'.Deg n y) (hD : C.D (n + 1) a = 0) (hP : Φ.tot a = C'.D n y) :
    Cl Φ n 0 (a 0) (y 0) := by
  refine ⟨fun s hs => ha 0 s hs, fun s hs => hy 0 s hs, ?_, ?_⟩
  · intro s t e
    have h1 := congrFun (congrFun hD 0) t
    rw [D_zero C (n + 1) a s t e] at h1
    exact h1
  · intro s t e
    have h1 := congrFun (congrFun hP 0) t
    rw [D_zero C' n y s t e] at h1
    exact h1

private theorem cl_next {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {a : C.Tot} {y : C'.Tot} {p : ℕ}
    (hC : C.Ok) (hC' : C'.Ok) (hΦ : Φ.Ok)
    (ha : C.Deg (n + 1) a) (hy : C'.Deg n y) (hD : C.D (n + 1) a = 0) (hP : Φ.tot a = C'.D n y)
    (x : St Φ n a y p) :
    Cl Φ n (p + 1) (fun s => a (p + 1) s - (n + 1).negOnePow • C.δ p s (x.u s))
      (fun s => y (p + 1) s + (n + 1).negOnePow • C'.δ p s (x.v s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [ha (p + 1) s hs, x.sv.su s (by omega), map_zero, smul_zero, sub_zero]
  · intro s hs
    simp only [hy (p + 1) s hs, x.sv.sv s (by omega), map_zero, smul_zero, add_zero]
  · intro s t e
    have h1 := congrFun (congrFun hD (p + 1)) t
    rw [D_succ C (n + 1) a p s t e, Int.negOnePow_succ, Units.neg_smul, x.hb t] at h1
    simp only [Pi.zero_apply] at h1
    have h2 : C.d (p + 1) s t (C.δ p s (x.u s)) = C.δ p t (x.b t) := by
      rw [hC.comm, x.sv.du s t e]
    simp only [map_sub, map_us, h2]
    rwa [← sub_eq_add_neg] at h1
  · intro s t e
    have h1 := congrFun (congrFun hP (p + 1)) t
    rw [D_succ C' n y p s t e] at h1
    change Φ (p + 1) t (a (p + 1) t) = _ at h1
    have h3 : C'.δ p t (y p t) =
        C'.δ p t (Φ p t (x.u t)) + C'.d (p + 1) s t (C'.δ p s (x.v s)) := by
      rw [x.hz t, x.sv.yv s t e, map_add, hC'.comm]
    have h4 : Φ (p + 1) t (C.δ p t (x.u t)) = C'.δ p t (Φ p t (x.u t)) := hΦ.2 p t (x.u t)
    simp only [map_sub, map_add, map_us, h4]
    rw [h1, h3, smul_add]
    abel

theorem UpperTheory.totalExact_of_columnExact :
    ∀ (C C' : DC) (Φ : C.Hom C'), C.Ok → C'.Ok → Φ.Ok → (∀ p, Φ.ColEx p) → Φ.TotEx := by
  intro C C' Φ hC hC' hΦ hcol n a y ha hy hD hP
  have hcl0 := cl_zero (Φ := Φ) ha hy hD hP
  have hs0 := solve (hcol 0) hcl0
  let S0 : St Φ n a y 0 := ⟨a 0, y 0, hs0.choose, hs0.choose_spec.choose, hcl0,
    hs0.choose_spec.choose_spec, fun _ => rfl, fun _ => rfl⟩
  let step : ∀ p, St Φ n a y p → St Φ n a y (p + 1) := fun p x =>
    { b := fun s => a (p + 1) s - (n + 1).negOnePow • C.δ p s (x.u s)
      z := fun s => y (p + 1) s + (n + 1).negOnePow • C'.δ p s (x.v s)
      u := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose
      v := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose_spec.choose
      cl := cl_next hC hC' hΦ ha hy hD hP x
      sv := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose_spec.choose_spec
      hb := fun s => by simp only [map_sub, map_us, hC.δδ, smul_zero, sub_zero]
      hz := fun s => by simp only [map_add, map_us, hC'.δδ, smul_zero, add_zero] }
  let S : ∀ p, St Φ n a y p := fun p => Nat.rec (motive := fun p => St Φ n a y p) S0 step p
  refine ⟨fun p s => (S p).u s, fun p s => (S p).v s, ?_, ?_, ?_, ?_⟩
  · intro p s hps
    exact (S p).sv.su s hps
  · intro p s hps
    exact (S p).sv.sv s hps
  · funext p t
    rcases p with _ | p
    · rw [D_zero C n _ (t - 1) t (by ring)]
      exact (S 0).sv.du (t - 1) t (by ring)
    · rw [D_succ C n _ p (t - 1) t (by ring)]
      have h1 := (S (p + 1)).sv.du (t - 1) t (by ring)
      change C.d (p + 1) (t - 1) t ((S (p + 1)).u (t - 1)) =
        a (p + 1) t - (n + 1).negOnePow • C.δ p t ((S p).u t) at h1
      beta_reduce
      rw [h1, sub_add_cancel]
  · funext p t
    rcases p with _ | p
    · show y 0 t = Φ 0 t ((S 0).u t) + C'.D (n - 1) (fun p s => (S p).v s) 0 t
      rw [D_zero C' (n - 1) _ (t - 1) t (by ring)]
      exact (S 0).sv.yv (t - 1) t (by ring)
    · show y (p + 1) t = Φ (p + 1) t ((S (p + 1)).u t) +
        C'.D (n - 1) (fun p s => (S p).v s) (p + 1) t
      rw [D_succ C' (n - 1) _ p (t - 1) t (by ring)]
      have h1 := (S (p + 1)).sv.yv (t - 1) t (by ring)
      change y (p + 1) t + (n + 1).negOnePow • C'.δ p t ((S p).v t) =
        Φ (p + 1) t ((S (p + 1)).u t) + C'.d (p + 1) (t - 1) t ((S (p + 1)).v (t - 1)) at h1
      have e : (n - 1 + 1).negOnePow = -(n + 1).negOnePow := by
        rw [sub_add_cancel, Int.negOnePow_succ, neg_neg]
      beta_reduce
      rw [e, Units.neg_smul, eq_sub_of_add_eq h1]
      abel
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.VectorBundleAffineRep
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

theorem UpperTheory.vector_bundle_affine_rep :
    ∀ (D : Type) [CommRing D] (d : ℕ) (U : (Spec (CommRingCat.of (MvPolynomial (Fin d) D))).Opens), IsCompl' (varIdeal (RingHom.id (MvPolynomial (Fin d) D))) U → ∃ φ : (Vec D d).psh ⟶ yoneda.obj (U : Scheme.{0}), (∀ (T : Scheme.{0}) (x : (Vec D d).obj Γ(T, ⊤)), φ.app (op T) x ≫ U.ι = specOf (ringOf ((Vec.toAff d).app _ x))) ∧ ∀ T : Scheme.{0}, IsAffine T → Function.Bijective (φ.app (op T)) := by
  intro D _ d U hU
  refine UpperTheory.represented_by_units (varIdeal (RingHom.id (MvPolynomial (Fin d) D))) U hU (Vec D d).psh
    (fun T x => ringOf ((Vec.toAff d).app Γ(T, ⊤) x)) ?_ ?_ ?_
  · intro T T' f x
    exact ringOf_map D f.appTop.hom ((Vec.toAff d).app Γ(T, ⊤) x)
  · intro T x
    rw [map_varIdeal, ← x.2]
    congr 2
    funext j
    simp [ringOf, Vec.toAff]
  · intro T ξ hξ
    rw [map_varIdeal] at hξ
    refine ⟨⟨(ξ.comp MvPolynomial.C, fun j => ξ (MvPolynomial.X j)), hξ⟩, ?_, ?_⟩
    · refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
      · simp [ringOf, Vec.toAff]
      · simp [ringOf, Vec.toAff]
    · intro y hy
      subst hy
      refine Subtype.ext (Prod.ext ?_ ?_)
      · ext c
        simp [ringOf, Vec.toAff]
      · funext j
        simp [ringOf, Vec.toAff]
end

