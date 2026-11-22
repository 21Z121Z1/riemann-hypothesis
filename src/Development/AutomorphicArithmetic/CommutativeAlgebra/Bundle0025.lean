import Mathlib
import Development.EtaleCohomology.EtaleSheaves.Bundle0041
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0004
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafCore
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0023
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0020
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveLineStdOpensBasicOpenGenerators
section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsMultivariableHensel

namespace UpperTheory.ProjectiveLineClosure

open GroundTheory.Arith.SchemeCoh ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem closure_chart (i j : Fin 2) (hij : i ≠ j) :
    Subring.closure {chartHom (A := ℤ) (n := 1) i (MvPolynomial.X j)} = ⊤ := by
  have hiso : IsIso (Proj.awayToSection (grading ℤ 1) (MvPolynomial.X i)) := by
    rw [← Proj.basicOpenIsoAway_hom (grading ℤ 1) (MvPolynomial.X i) (X_mem i) one_pos]
    infer_instance
  have hsurj := (ConcreteCategory.bijective_of_isIso (Proj.awayToSection (grading ℤ 1) (MvPolynomial.X i))).2
  have hpoly : ∀ a : MvPolynomial (Fin (1 + 1)) ℤ,
      chartHom (A := ℤ) (n := 1) i a ∈ Subring.closure {chartHom (A := ℤ) (n := 1) i (MvPolynomial.X j)} := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
      rw [show (MvPolynomial.C c : MvPolynomial (Fin (1 + 1)) ℤ) = (c : MvPolynomial (Fin (1 + 1)) ℤ) from
        eq_intCast MvPolynomial.C c, map_intCast]
      exact intCast_mem _ c
    | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    | mul_X p n hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      by_cases hn : n = i
      · subst hn
        rw [chartHom_X_self]
        exact one_mem _
      · have hnj : n = j := by
          fin_cases n <;> fin_cases i <;> fin_cases j <;> simp_all
        subst hnj
        exact Subring.subset_closure rfl
  rw [eq_top_iff]
  intro s _
  obtain ⟨y, rfl⟩ := hsurj s
  obtain ⟨k, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem i) y
  have ha' : a ∈ grading ℤ 1 k := by simpa using ha
  convert hpoly a using 1
  exact (chartHom_of_mem i ha').symm

private theorem chartHom_eq_ratio (i j : Fin 2) :
    chartHom (A := ℤ) (n := 1) i (MvPolynomial.X j) =
      ProjTwist.ratio (grading ℤ 1) (X_mem i) (X_mem j) := by
  rw [chartHom_of_mem i (X_mem j)]
  unfold ProjTwist.ratio
  congr 1
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk]

private theorem mul_res :
    resR (inf_le_left : stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1 ≤ stdOpen ℤ 1 0)
        (chartHom (A := ℤ) (n := 1) 0 (MvPolynomial.X 1)) *
      resR (inf_le_right : stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1 ≤ stdOpen ℤ 1 1)
        (chartHom (A := ℤ) (n := 1) 1 (MvPolynomial.X 0)) = 1 := by
  have h := ProjTwist.ratio_mul_ratio' (𝒜 := grading ℤ 1) (X_mem (A := ℤ) (n := 1) 0)
    (X_mem (A := ℤ) (n := 1) 1) (X_mem (A := ℤ) (n := 1) 0)
  rw [ProjTwist.ratio_self] at h
  rw [chartHom_eq_ratio, chartHom_eq_ratio, mul_comm]
  exact h.trans (map_one _)

end UpperTheory.ProjectiveLineClosure

open GroundTheory.Arith.SchemeCoh ProjSpace UpperTheory.ProjectiveLineClosure in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem UpperTheory.projectiveLine_std_opens_basicOpen_generators :
    ∃ (τ : Γ(P1, stdOpen 0)) (σ : Γ(P1, stdOpen 1)),
        IsAffineOpen (stdOpen 0) ∧ IsAffineOpen (stdOpen 1) ∧
        Subring.closure {τ} = ⊤ ∧ Subring.closure {σ} = ⊤ ∧
        P1.basicOpen τ = stdOpen 0 ⊓ stdOpen 1 ∧ P1.basicOpen σ = stdOpen 0 ⊓ stdOpen 1 ∧
        P1.presheaf.map (homOfLE (inf_le_left : stdOpen 0 ⊓ stdOpen 1 ≤ stdOpen 0)).op τ *
          P1.presheaf.map (homOfLE (inf_le_right : stdOpen 0 ⊓ stdOpen 1 ≤ stdOpen 1)).op σ = 1 := by
  refine ⟨chartHom (A := ℤ) (n := 1) 0 (MvPolynomial.X 1),
    chartHom (A := ℤ) (n := 1) 1 (MvPolynomial.X 0),
    isAffineOpen_stdOpen (A := ℤ) (n := 1) 0, isAffineOpen_stdOpen (A := ℤ) (n := 1) 1,
    closure_chart 0 1 (by decide), closure_chart 1 0 (by decide),
    basicOpen_chartHom_X (A := ℤ) (n := 1) 0 1, ?_, ?_⟩
  · refine (basicOpen_chartHom_X (A := ℤ) (n := 1) 1 0).trans ?_
    exact inf_comm _ _
  · exact mul_res
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RelativeCohomologyIsTotalModelOfImage
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.VanishingEvaluation

variable {R : Type} [CommRing R]

private noncomputable abbrev pb {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n) :
    Cochain ((chains R).obj E) K n :=
  (Cochain.ofHom ((chains R).map f)).comp α (zero_add n)

private theorem pb_sub {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E') K n) :
    pb f (α - β) = pb f α - pb f β :=
  Cochain.comp_sub _ _ _ _

private theorem ev_pb {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (pb f α) p s h U x = ev α p s h U (x.map f) :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.2.1 f α p s h U x

private theorem ev_zero {E : Spc} {K : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (0 : Cochain ((chains R).obj E) K n) p s h U x = 0 :=
  ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 0 0 p s h U x).2.2.1

private theorem pb_eq_zero {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev α p s h U (x.map f) = 0) :
    pb f α = 0 :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 _ _ fun p s h' U x => by rw [ev_pb, h, ev_zero]

private theorem δ_pb {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n) (n' : ℤ) :
    δ n n' (pb f α) = pb f (δ n n' α) := by
  by_cases h : n + 1 = n'
  · rw [δ_comp _ _ (zero_add n) 1 n' n' h (zero_add 1) h]; simp
  · simp [δ_shape _ _ h]

private theorem δ_van {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n) (n' : ℤ)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev α p s h U (x.map f) = 0)
    (p : ℕ) (s : ℤ) (h' : -(p : ℤ) + n' = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (δ n n' α) p s h' U (x.map f) = 0 := by
  rw [← ev_pb, ← δ_pb, pb_eq_zero f α h, δ_zero, ev_zero]

private theorem dbl_ext (P : Arrow Spc) {K : Cx R} {N : ℤ} (α β : Cochain ((chains R).obj (dbl P)) K N)
    (hl : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev α p s h U (z.map (dbl.inl P)) = ev β p s h U (z.map (dbl.inl P)))
    (hr : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev α p s h U (z.map (dbl.inr P)) = ev β p s h U (z.map (dbl.inr P))) : α = β :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 α β fun p s h U w => by
    rcases (UpperTheory.doubleMappingCylinder_cochain_extension R P).1 p U w with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact hl p s h U z
    · exact hr p s h U z

private theorem map_map {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    (x.map f).map g = x.map (f ≫ g) := rfl

private theorem map_id {E : Spc} {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) : x.map (𝟙 E) = x := rfl

private theorem van_img (P : Arrow Spc) {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj (dbl P)) K n)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev α p s h U (z.map (dbl.inr P)) = 0)
    (p : ℕ) (s : ℤ) (h' : -(p : ℤ) + n = s) (U : Scheme.{0}) (z : Sx P.right p U)
    (hz : (Sub.img P.hom).mem p U z) : ev α p s h' U (z.map (dbl.inl P)) = 0 := by
  obtain ⟨y, rfl⟩ := hz
  have e : (y.map P.hom).map (dbl.inl P) = (y.map P.hom).map (dbl.inr P) := by
    rw [map_map, map_map]
    exact congrArg (fun f => Sx.map f y) (pushout.condition : P.hom ≫ pushout.inl P.hom P.hom = P.hom ≫ pushout.inr P.hom P.hom)
  rw [e]
  exact h p s h' U _

private theorem pb_fold (P : Arrow Spc) {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj P.right) K n) :
    pb (dbl.inr P) (pb (dbl.fold P) α) = α :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 _ _ fun p s h U x => by
    rw [ev_pb, ev_pb, map_map, dbl.inr_fold, map_id]

private theorem comp_eq {E E' : Spc} {j : E ⟶ E'} {Z : Sub E} {K : Cx R} {m N : ℤ}
    {γ γ' : Cochain ((chains R).obj E') K N} {x : (famDC Z K m).Tot} (h : Comp j γ x) (h' : Comp j γ' x)
    (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx E p U) :
    ev γ p s hs U (z.map j) = ev γ' p s hs U (z.map j) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + m := ⟨s - m, by omega⟩
  exact (h p t hs U z).symm.trans (h' p t hs U z)

private theorem comp_zero {E E' : Spc} (j : E ⟶ E') (Z : Sub E) (K : Cx R) (m N : ℤ) :
    Comp j (0 : Cochain ((chains R).obj E') K N) (0 : (famDC Z K m).Tot) := by
  intro p s h U z
  exact (ev_zero p _ h U (z.map j)).symm

private theorem pull_inr (q : ℕ) (P : Arrow Spc) (i N : ℤ) (g : Cocycle ((chains (ZMod q)).obj (dbl P)) (res _ (tw q i)) N)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev g.1 p s h U (z.map (dbl.inr P)) = 0) :
    pull _ (dbl.inr P) (tw q i) N (CohomologyClass.mk g) = 0 := by
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (dbl.inr P))) g (zero_add N)) = 0
  have e : zcomp (Cocycle.ofHom ((chains (ZMod q)).map (dbl.inr P))) g (zero_add N) = 0 :=
    Cocycle.ext (pb_eq_zero _ _ h)
  rw [e, CohomologyClass.mk_zero]

end UpperTheory.VanishingEvaluation

open UpperTheory.VanishingEvaluation in
theorem UpperTheory.relativeCohomology_isTotalModel_of_image :
    ∀ (q : ℕ) (P : Arrow Spc) (i m n N : ℤ), n + m = N → TModel (famDC (Sub.img P.hom) (res _ (tw q i)) m) n (fun x (c : Hs q P N i) => SRel (N := N) x c.1) := by
  intro q P i m n N hN
  have C := fun n N h => UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain (ZMod q) (dbl.inl P) (Sub.img P.hom) (res _ (tw q i)) m n N h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hD
    obtain ⟨γ, hγ, hv⟩ := (UpperTheory.doubleMappingCylinder_cochain_extension (ZMod q) P).2 (res _ (tw q i)) m N x
    have h0 : δ N (N + 1) γ = 0 := by
      have hc := (C n N hN).2.2.1 γ x hγ
      rw [hD] at hc
      refine dbl_ext P _ _ (comp_eq hc (comp_zero _ _ _ _ _)) fun p s h U z => ?_
      rw [δ_van _ _ _ hv, ev_zero]
    refine ⟨⟨CohomologyClass.mk (Cocycle.mk γ (N + 1) rfl h0), ?_⟩, Cocycle.mk γ (N + 1) rfl h0, rfl, hγ, hv⟩
    exact pull_inr q P i N _ hv
  · rintro ⟨c, hc⟩
    obtain ⟨g₀, rfl⟩ := CohomologyClass.mk_surjective c
    have hc' : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (dbl.inr P))) g₀ (zero_add N)) = 0 := hc
    rw [CohomologyClass.mk_eq_zero_iff] at hc'
    obtain ⟨N', hN', β, hβ⟩ := hc'
    have hβ' : δ N' N β = pb (dbl.inr P) g₀.1 := hβ
    let e : Cocycle ((chains (ZMod q)).obj (dbl P)) (res _ (tw q i)) N :=
      Cocycle.mk (δ N' N (pb (dbl.fold P) β)) (N + 1) rfl (δ_δ _ _ _ _)
    have he : CohomologyClass.mk e = 0 := by
      rw [CohomologyClass.mk_eq_zero_iff]
      exact ⟨N', hN', _, rfl⟩
    have hm : CohomologyClass.mk (g₀ - e) = CohomologyClass.mk g₀ := by
      rw [CohomologyClass.mk_sub, he, sub_zero]
    have hp : pb (dbl.inr P) (g₀ - e).1 = 0 := by
      change pb (dbl.inr P) (g₀.1 - δ N' N (pb (dbl.fold P) β)) = 0
      rw [pb_sub, ← δ_pb, pb_fold, hβ', sub_self]
    have hv : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
        ev (g₀ - e).1 p s h U (z.map (dbl.inr P)) = 0 := fun p s h U z => by
      rw [← ev_pb, hp, ev_zero]
    obtain ⟨x, hd, hx⟩ := (C n N hN).1 (g₀ - e).1 (van_img P _ hv)
    refine ⟨x, hd, ?_, g₀ - e, hm, hx, hv⟩
    refine (C (n + 1) (N + 1) (by omega)).2.1 (δ N (N + 1) (g₀ - e).1) _ 0 ((C n N hN).2.2.2.2 x hd)
      (fun _ _ _ => rfl) ((C n N hN).2.2.1 _ x hx) ?_
    rw [(g₀ - e).δ_eq_zero]
    exact comp_zero _ _ _ _ _
  · rintro x c x' c' ⟨g, hg, hc, hv⟩ ⟨g', hg', hc', hv'⟩
    refine ⟨g - g', ?_, (C n N hN).2.2.2.1 _ _ _ _ hc hc', fun p s h U z => ?_⟩
    · rw [CohomologyClass.mk_sub, hg, hg']; rfl
    · have := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 g.1 g'.1 p s h U (z.map (dbl.inr P))).2.1
      rw [hv, hv', sub_zero] at this
      exact this
  · rintro x c hd ⟨g, hg, hc, hv⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have hN' : n' + m = N' := by omega
    simp only [add_sub_cancel_right]
    constructor
    · intro h0
      have hz : CohomologyClass.mk g = 0 := by rw [hg, h0]; rfl
      rw [CohomologyClass.mk_eq_zero_iff] at hz
      obtain ⟨M, hM, β, hβ⟩ := hz
      obtain rfl : M = N' := by omega
      have hβ' : δ M (M + 1) β = g.1 := hβ
      have hp : pb (dbl.inr P) g.1 = 0 := pb_eq_zero _ _ hv
      have hb : δ M (M + 1) (β - pb (dbl.fold P) (pb (dbl.inr P) β)) = g.1 := by
        rw [δ_sub, δ_pb, δ_pb, hβ', hp]
        simp
      have hp' : pb (dbl.inr P) (β - pb (dbl.fold P) (pb (dbl.inr P) β)) = 0 := by
        rw [pb_sub, pb_fold, sub_self]
      have hv' : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + M = s) (U : Scheme.{0}) (z : Sx P.right p U),
          ev (β - pb (dbl.fold P) (pb (dbl.inr P) β)) p s h U (z.map (dbl.inr P)) = 0 := fun p s h U z => by
        rw [← ev_pb, hp', ev_zero]
      obtain ⟨y, hy, hcy⟩ := (C n' M hN').1 _ (van_img P _ hv')
      refine ⟨y, hy, ?_⟩
      have h1 := (C n' M hN').2.2.1 _ y hcy
      rw [hb] at h1
      exact (C (n' + 1) (M + 1) (by omega)).2.1 g.1 _ x ((C n' M hN').2.2.2.2 y hy) hd h1 hc
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨β, hβ, hvβ⟩ := (UpperTheory.doubleMappingCylinder_cochain_extension (ZMod q) P).2 (res _ (tw q i)) m N' y
      have e : g.1 = δ N' (N' + 1) β :=
        dbl_ext P _ _ (comp_eq hc ((C n' N' hN').2.2.1 β y hβ)) fun p s h U z => by
          rw [hv, δ_van _ _ _ hvβ]
      apply Subtype.ext
      change c.1 = 0
      rw [← hg, CohomologyClass.mk_eq_zero_iff]
      exact ⟨N', rfl, β, e.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RelativeCupProductLevelwiseCompat
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem units_map_smul {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (η : ℤˣ) (x : A) :
    f (η • x) = η • f x := by
  simp [Units.smul_def]

private theorem colEx_transfer {C C' D D' : DC} (Φ : C.Hom C') (Ψ : D.Hom D') (p : ℕ) (η : ℤˣ)
    (e : ∀ s, C.A p s ≃+ D.A 0 s) (e' : ∀ s, C'.A p s ≃+ D'.A 0 s)
    (hd : ∀ s t x, e t (C.d p s t x) = D.d 0 s t (e s x))
    (hd' : ∀ s t x, e' t (C'.d p s t x) = D'.d 0 s t (e' s x))
    (hΦ : ∀ s x, e' s (Φ p s x) = η • Ψ 0 s (e s x)) (h : Ψ.ColEx 0) : Φ.ColEx p := by
  have hηη : ∀ {A : Type 1} [AddCommGroup A] (x : A), η • η • x = x := fun x => by
    rw [smul_smul, Int.units_mul_self, one_smul]
  intro s a y ha hy
  have hΨ : ∀ s x, Ψ 0 s (e s x) = η • e' s (Φ p s x) := fun s x => by rw [hΦ, hηη]
  obtain ⟨a', y', h1, h2⟩ := h s (e _ a) (η • e' s y)
    (by rw [← hd, ha, map_zero])
    (by rw [hΨ, hy, hd', units_map_smul])
  refine ⟨(e s).symm a', η • (e' _).symm y', ?_, ?_⟩
  · apply (e _).injective
    rw [hd, AddEquiv.apply_symm_apply, h1]
  · apply (e' _).injective
    have h3 : e' s y = η • (Ψ 0 s a' + D'.d 0 (s - 1) s y') := by rw [← h2, hηη]
    have h4 : e' (s - 1) (η • (e' (s - 1)).symm y') = η • y' := by
      have := units_map_smul (e' (s - 1)).toAddMonoidHom η ((e' (s - 1)).symm y')
      simpa using this
    rw [h3, map_add, hΦ, hd', AddEquiv.apply_symm_apply, h4, units_map_smul, smul_add]

private def lvl {R : Type} [CommRing R] {E : Spc} {p : ℕ} (Z : Sub E)
    (Z' : Sub (disc.obj (E.obj (op (SimplexCategory.mk p)))))
    (h : ∀ (W : Scheme.{0}) (z : Sx E p W), Z'.mem 0 W z ↔ Z.mem p W z) (M : Shv R) :
    Fam Z p M ≃+ Fam Z' 0 M where
  toFun a := ⟨a.1, a.2.1, fun U x hx => a.2.2 U x ((h U x).1 hx)⟩
  invFun a := ⟨a.1, a.2.1, fun U x hx => a.2.2 U x ((h U x).2 hx)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private theorem disc_δ {R : Type} [CommRing R] {F : PSh} (Z : Sub (disc.obj F)) (L : Cx R) (m s : ℤ)
    (x : (famDC Z L m).A 0 s) : (famDC Z L m).δ 0 s x = 0 := by
  apply Subtype.ext
  funext U z
  have hf : ∀ i, Sx.face (E := disc.obj F) z i = z := fun _ => rfl
  change m.negOnePow • ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (show Fam Z 0 (L.X (s + m)) from x).1 U (Sx.face (E := disc.obj F) z i) = 0
  simp [Fin.sum_univ_two, hf]

private theorem fam_smul {R : Type} [CommRing R] {E : Spc} (Z : Sub E) (p : ℕ) (M : Shv R) (η : ℤˣ) (a : Fam Z p M)
    (W : Scheme.{0}) (z : Sx E p W) : (η • a).1 W z = η • a.1 W z := by
  rcases Int.units_eq_one_or η with rfl | rfl <;> simp

theorem UpperTheory.relativeCupProduct_levelwise_compat :
    ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m : ℤ) (β : Sec (J.X m) X) (p : ℕ)
    (Φ : (famDC (Sub.bot E) I 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) K m))
    (Ψ : (famDC (Sub.bot (disc.obj (E.obj (op (SimplexCategory.mk p))))) I 0).Hom (famDC (Sub.img (E := disc.obj (E.obj (op (SimplexCategory.mk p)))) (pullback.fst (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) (sch.map U.ι))) K m)),
    IsProd μ π β Φ → IsProd μ (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) β Ψ → Ψ.TotEx → Φ.ColEx p := by
  intro R _ I J K μ X U E π m β p Φ Ψ hΦ hΨ hT
  have h0 : Ψ.ColEx 0 := UpperTheory.columnExact_zero_of_totalExact_of_vertical_zero _ _ Ψ (disc_δ _ _ _) (disc_δ _ _ _) hT
  have hbot : ∀ (W : Scheme.{0}) (z : Sx E p W),
      (Sub.bot (disc.obj (E.obj (op (SimplexCategory.mk p))))).mem 0 W z ↔ (Sub.bot E).mem p W z :=
    fun _ _ => Iff.rfl
  have himg : ∀ (W : Scheme.{0}) (z : Sx E p W),
      (Sub.img (E := disc.obj (E.obj (op (SimplexCategory.mk p)))) (pullback.fst (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) (sch.map U.ι))).mem 0 W z ↔
        (Sub.img (E := E) (pullback.fst π (sch.map U.ι))).mem p W z := fun W z =>
    ((UpperTheory.mem_pullbackImage_iff_factors_through_open U (show disc.obj (E.obj (op (SimplexCategory.mk p))) ⟶ sch.obj X from disc.map (π.app (op (SimplexCategory.mk p)))) 0 W z).1).trans
      ((UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).1).symm
  refine colEx_transfer Φ Ψ p (m * (p : ℤ)).negOnePow (fun s => lvl _ _ hbot _) (fun s => lvl _ _ himg _)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) ?_ h0
  intro s x
  apply Subtype.ext
  funext W z
  have h1 := hΦ p s x W z
  have h2 := hΨ 0 s (lvl _ _ hbot _ x) W z
  refine Eq.trans h1 (Eq.trans ?_ (fam_smul _ _ _ (m * (p : ℤ)).negOnePow (Ψ 0 s (lvl _ _ hbot _ x)) W z).symm)
  refine congrArg _ (Eq.trans ?_ h2.symm)
  have h0' : (m * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
  rw [h0', one_smul]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RelativeCupProductRealizesProductOfRepresentativ
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem inl_fold' (P : Arrow Spc) : dbl.inl P ≫ dbl.fold P = 𝟙 _ := pushout.inl_desc _ _ _

private theorem inl_map' {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc _ _ _

private theorem aw_last {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {D : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj D) I n) (β : Cochain ((chains R).obj D) J m) {W : Scheme.{0}} {p : ℕ}
    (x : Sx D p W) (b : Sec (J.X m) W) (hp : p + 0 ≤ p)
    (hb : ev β 0 m (by simp) W (x.sub p 0 hp) = b) (r k : ℕ) (hr : r = p) (hk : k = 0) (s t w : ℤ) (h : s + t = w)
    (hs : -(r : ℤ) + n = s) (ht : -(k : ℤ) + m = t) (h0 : 0 + r ≤ p) (h1 : r + k ≤ p)
    (s' : ℤ) (hs' : -(p : ℤ) + n = s') (h' : s' + m = w) :
    μ.mul W s t w h (ev α r s hs W (x.sub 0 r h0)) (ev β k t ht W (x.sub r k h1)) =
      μ.mul W s' m w h' (ev α p s' hs' W x) b := by
  subst hr hk
  have ht' : m = t := by simpa using ht
  subst ht'
  subst hs
  subst hs'
  rw [(GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite x).2.1, hb]

private theorem aw_eval {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {D : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj D) I n) (β : Cochain ((chains R).obj D) J m)
    (γ : Cochain ((chains R).obj D) K (n + m)) (hγ : μ.IsAW rfl α β γ)
    (hβ : ∀ (k : ℕ), 0 < k → ∀ (s : ℤ) h (W : Scheme.{0}) (y : Sx D k W), ev β k s h W y = 0)
    {W : Scheme.{0}} {p : ℕ} (x : Sx D p W) (b : Sec (J.X m) W) (hp : p + 0 ≤ p)
    (hb : ev β 0 m (by simp) W (x.sub p 0 hp) = b) (w : ℤ) (h : -(p : ℤ) + (n + m) = w)
    (s : ℤ) (hs : -(p : ℤ) + n = s) (h' : s + m = w) :
    ev γ p w h W x = (m * (p : ℕ)).negOnePow • μ.mul W s m w h' (ev α p s hs W x) b := by
  rw [hγ p w h W x, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
  · exact congrArg _ (aw_last μ α β x b hp hb _ _ rfl (Nat.sub_self p) _ _ _ _ _ _ _ _ s hs h')
  · intro r _
    have hk : 0 < p - ((Fin.castSucc r : Fin (p + 1)) : ℕ) := by
      have := r.2
      simp only [Fin.val_castSucc]
      omega
    rw [hβ _ hk, map_zero, smul_zero]

private theorem last_vertex {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) {p : ℕ} {W : Scheme.{0}}
    (z : Sx E p W) (h : p + 0 ≤ p) (ι' : E ⟶ dbl (abv U π)) (ι : sch.obj X ⟶ dbl (opn U))
    (hι : ι' ≫ dbl.map (abvMap U π) = π ≫ ι) :
    ((z.map ι').sub p 0 h).map (dbl.map (abvMap U π)) = Sx.map (E := sch.obj X) (p := 0) ι (under π z) := by
  rw [((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite z).2.2.1 p 0 h).2.1 ι']
  have h1 : ((z.sub p 0 h).map ι').map (dbl.map (abvMap U π)) = (z.sub p 0 h).map (ι' ≫ dbl.map (abvMap U π)) := rfl
  rw [h1, hι]
  have h2 : (z.sub p 0 h).map (π ≫ ι) = Sx.map (E := sch.obj X) (p := 0) ι (under π (z.sub p 0 h)) := rfl
  rw [h2, ((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite z).2.2.1 p 0 h).2.2, (UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).2.2 0 _]

theorem UpperTheory.relativeCupProduct_realizes_product_of_representative :
    LeafAW → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m j i n : ℤ) (c : Hs q (opn U) m j) (β : Sec ((res _ (tw q j)).X m) X), IsRep U β c.1 →
    ∀ Φ : (famDC (Sub.bot E) (res _ (tw q i)) 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) (res _ (tw q (i + j))) m), IsProd (twPair q i j) π β Φ →
    ∀ (x : (famDC (Sub.bot E) (res _ (tw q i)) 0).Tot) (a : Ht q E n i), HRel x a → SRel (P := abv U π) (N := n + m) (Φ.tot x) (Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c)).1 := by
  intro hAW q _ X U E π m j i n c β hrep Φ hΦ x a hx
  obtain ⟨-, -, γ₀, hγ₀, h0l, h0r, h0p⟩ := hrep
  obtain ⟨α, hα, hαx⟩ := hx
  let α' : Cocycle ((chains _).obj (dbl (abv U π))) (res _ (tw q i)) n :=
    zcomp (Cocycle.ofHom ((chains _).map (dbl.fold (abv U π)))) α (zero_add n)
  let β' : Cocycle ((chains _).obj (dbl (abv U π))) (res _ (tw q j)) m :=
    zcomp (Cocycle.ofHom ((chains _).map (dbl.map (abvMap U π)))) γ₀ (zero_add m)
  obtain ⟨γ, hγ, hcup⟩ := (hAW q i j).2 (dbl (abv U π)) n m α' β'
  have evα : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) p W),
      ev α'.1 p s h W y = ev α.1 p s h W (y.map (dbl.fold (abv U π))) := fun p s h W y =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.fold (abv U π)) α.1 p s h W y
  have evβ : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) p W),
      ev β'.1 p s h W y = ev γ₀.1 p s h W (y.map (dbl.map (abvMap U π))) := fun p s h W y =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.map (abvMap U π)) γ₀.1 p s h W y
  have hvan : ∀ (k : ℕ), 0 < k → ∀ (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) k W), ev β'.1 k s h W y = 0 := by
    intro k hk s h W y
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [evβ]
    exact h0p k s _ W _
  have hinr : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (z : Sx (abv U π).right p W),
      ev γ.1 p s h W (z.map (dbl.inr (abv U π))) = 0 := by
    intro p s h W z
    have hb : ev β'.1 0 m (by simp) W ((z.map (dbl.inr (abv U π))).sub p 0 (by omega)) = 0 := by
      rw [evβ]
      refine (congrArg (fun y => ev γ₀.1 0 m (by simp) W y)
        (last_vertex U π z (by omega) (dbl.inr (abv U π)) (dbl.inr (opn U)) (dbl.inr_map (abvMap U π)))).trans ?_
      exact h0r W _
    rw [aw_eval _ α'.1 β'.1 γ.1 hγ hvan _ 0 (by omega) hb s h (-(p : ℤ) + n) rfl (by omega), map_zero, smul_zero]
  refine ⟨γ, ?_, ?_, hinr⟩
  · have hC : cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1 = CohomologyClass.mk γ := by
      rw [← hcup, ← hα]
      change cup q _ (pull _ (dbl.map (abvMap U π)) _ m c.1) = _
      rw [← hγ₀]
      rfl
    have hz : pull _ (dbl.inr (abv U π)) (tw q (i + j)) (n + m) (CohomologyClass.mk γ) = 0 := by
      have h0 : zcomp (Cocycle.ofHom ((chains _).map (dbl.inr (abv U π)))) γ (zero_add (n + m)) = 0 := by
        have hc : (zcomp (Cocycle.ofHom ((chains _).map (dbl.inr (abv U π)))) γ (zero_add (n + m))).1 = 0 := by
          refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.1 _ _ fun p s h W z => ?_
          rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).1 0 0 p s h W z).2.2.1]
          exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.inr (abv U π)) γ.1 p s h W z).trans (hinr p s h W z)
        exact Cocycle.ext hc
      exact (congrArg CohomologyClass.mk h0).trans (CohomologyClass.mk_zero _ _ _)
    change CohomologyClass.mk γ = cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1 -
      pull _ (dbl.fold (abv U π)) _ _ (pull _ (dbl.inr (abv U π)) _ _
        (cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1))
    rw [hC, hz, map_zero, sub_zero]
  · intro p s h W z
    have hs : -(p : ℤ) + n = s + 0 := by omega
    have hb : ev β'.1 0 m (by simp) W ((z.map (dbl.inl (abv U π))).sub p 0 (by omega)) = Sec.res (under π z) β := by
      rw [evβ]
      refine (congrArg (fun y => ev γ₀.1 0 m (by simp) W y)
        (last_vertex U π z (by omega) (dbl.inl (abv U π)) (dbl.inl (opn U)) (inl_map' (abvMap U π)))).trans ?_
      exact h0l W _
    have e := hΦ p s (x p s) W z
    rw [hαx p s hs W z] at e
    refine e.trans ?_
    rw [aw_eval _ α'.1 β'.1 γ.1 hγ hvan _ _ (by omega) hb (s + m) h (s + 0) hs (by omega), evα]
    have hf : (z.map (dbl.inl (abv U π))).map (dbl.fold (abv U π)) = z.map (𝟙 E) := by
      have h1 : (z.map (dbl.inl (abv U π))).map (dbl.fold (abv U π)) = z.map (dbl.inl (abv U π) ≫ dbl.fold (abv U π)) := rfl
      rw [h1, inl_fold']
      rfl
    rw [hf]
end

