import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0374
import Development.EtaleCohomology.EtaleSheaves.Bundle0016
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0016
import GroundTheory.FunctionField.Bundle0001
import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import Development.EtaleCohomology.EtaleSheaves.ProperLineCovers.CoverPf
import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.DoubleMappingCylinderCochainExtension
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.PushoutCovers

private noncomputable def Fe (p : ℕ) (U : Scheme.{0}) : Spc ⥤ Type 1 :=
  ((evaluation _ _).obj (op (SimplexCategory.mk p))) ⋙ ((evaluation _ _).obj (op U)) ⋙ uliftFunctor.{1, 0}

private theorem po (P : Arrow Spc) (p : ℕ) (U : Scheme.{0}) :
    IsPushout ((Fe p U).map P.hom) ((Fe p U).map P.hom) ((Fe p U).map (dbl.inl P)) ((Fe p U).map (dbl.inr P)) := by
  have : PreservesColimit (span P.hom P.hom) (Fe p U) := by
    unfold Fe
    infer_instance
  exact (IsPushout.of_hasPushout P.hom P.hom).map (Fe p U)

private theorem cover (P : Arrow Spc) (p : ℕ) (U : Scheme.{0}) (w : Sx (dbl P) p U) :
    (∃ z : Sx P.right p U, z.map (dbl.inl P) = w) ∨ ∃ z : Sx P.right p U, z.map (dbl.inr P) = w := by
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit (po P p U).isColimit (ULift.up w)
  rcases j with _ | j
  · left
    exact ⟨Sx.map P.hom y.down, congrArg ULift.down hy⟩
  · cases j
    · left
      exact ⟨y.down, congrArg ULift.down hy⟩
    · right
      exact ⟨y.down, congrArg ULift.down hy⟩

private theorem fn (P : Arrow Spc) (p : ℕ) (U : Scheme.{0}) {T : Type 1} [Zero T] (f : Sx P.right p U → T)
    (hf : ∀ y : Sx P.left p U, f (y.map P.hom) = 0) :
    ∃ φ : Sx (dbl P) p U → T, (∀ z : Sx P.right p U, φ (z.map (dbl.inl P)) = f z) ∧ ∀ z : Sx P.right p U, φ (z.map (dbl.inr P)) = 0 := by
  have h := po P p U
  let d : (Fe p U).obj (dbl P) ⟶ T :=
    h.desc (TypeCat.ofHom fun z => f z.down) (TypeCat.ofHom fun _ => 0) (by
      ext y
      exact hf y.down)
  refine ⟨fun w => d (ULift.up w), fun z => ?_, fun z => ?_⟩
  · exact ConcreteCategory.congr_hom (CC := fun X => X) (h.inl_desc _ _ _)
      (ULift.up z : ULift.{1} (Sx P.right p U))
  · exact ConcreteCategory.congr_hom (CC := fun X => X) (h.inr_desc _ _ _)
      (ULift.up z : ULift.{1} (Sx P.right p U))

private theorem res_map {E E' : Spc} (f : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (z : Sx E p U) :
    (z.map f).res g = (z.res g).map f := by
  exact (FunctorToTypes.naturality (f.app _) g.op z).symm

end UpperTheory.PushoutCovers

open UpperTheory.PushoutCovers in
theorem UpperTheory.doubleMappingCylinder_cochain_extension :
    ∀ (R : Type) [CommRing R] (P : Arrow Spc), (∀ (p : ℕ) (U : Scheme.{0}) (w : Sx (dbl P) p U), (∃ z : Sx P.right p U, z.map (dbl.inl P) = w) ∨ ∃ z : Sx P.right p U, z.map (dbl.inr P) = w) ∧
    ∀ (K : Cx R) (m N : ℤ) (x : (famDC (Sub.img P.hom) K m).Tot), ∃ γ : Cochain ((chains R).obj (dbl P)) K N, Comp (dbl.inl P) γ x ∧ ∀ (p : ℕ) (s : ℤ) h (U : Scheme.{0}) (z : Sx P.right p U), ev γ p s h U (z.map (dbl.inr P)) = 0 := by
  intro R _ P
  refine ⟨fun p U w => cover P p U w, ?_⟩
  intro K m N x
  have key : ∀ (p : ℕ) (s' : ℤ) (U : Scheme.{0}), ∃ φ : Sx (dbl P) p U → Sec (K.X s') U,
      ∀ (s : ℤ) (e : s + m = s'), ∀ z : Sx P.right p U,
        φ (z.map (dbl.inl P)) = e ▸ (x p s).1 U z ∧ φ (z.map (dbl.inr P)) = 0 := by
    intro p s' U
    obtain ⟨s, rfl⟩ : ∃ s, s' = s + m := ⟨s' - m, by ring⟩
    obtain ⟨φ, h1, h2⟩ := fn P p U (T := Sec (K.X (s + m)) U) ((x p s).1 U)
      (fun y => (x p s).2.2 U _ ⟨y, rfl⟩)
    refine ⟨φ, fun s1 e z => ?_⟩
    obtain rfl : s1 = s := by omega
    exact ⟨h1 z, h2 z⟩
  choose φ hφ using key
  have nat : ∀ (p : ℕ) (s' : ℤ) (_ : -(p : ℤ) + N = s') (V U : Scheme.{0}) (g : V ⟶ U)
      (w : Sx (dbl P) p U), Sec.res g (φ p s' U w) = φ p s' V (Sx.res g w) := by
    intro p s' _ V U g w
    obtain ⟨s, rfl⟩ : ∃ s, s' = s + m := ⟨s' - m, by ring⟩
    rcases cover P p U w with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · rw [(hφ p (s + m) U s rfl z).1, res_map, (hφ p (s + m) V s rfl _).1]
      exact (x p s).2.1 V U g z
    · rw [(hφ p (s + m) U s rfl z).2, res_map, (hφ p (s + m) V s rfl _).2]
      exact map_zero _
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' R (E := dbl P) (I := K) (n := N) (fun p s' _ U => φ p s' U) nat
  refine ⟨γ, fun p s h U z => ?_, fun p s h U z => ?_⟩
  · rw [hγ]
    exact ((hφ p (s + m) U s rfl z).1).symm
  · rw [hγ]
    exact (hφ p s U (s - m) (by ring) z).2
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIdempotentSubmonoidIsLocalizationAtPrime
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace LateralTheory.E.BuildCut

theorem UpperTheory.exists_idempotent_submonoid_isLocalization_atPrime :
    ∀ {W : Type} [CommRing W], ProdACF W → ∀ (q : PrimeSpectrum W),
        ∃ T : Submonoid W, (∀ s ∈ T, IsIdempotentElem s ∧ s ∉ q.asIdeal) ∧ IsLocalization T (Localization.AtPrime q.asIdeal) := by
  intro W _ hW q
  let T : Submonoid W :=
    { carrier := {s | IsIdempotentElem s ∧ s ∉ q.asIdeal}
      one_mem' := ⟨IsIdempotentElem.one, (Ideal.ne_top_iff_one _).mp q.isPrime.ne_top⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨ha.1.mul hb.1, fun h => (q.isPrime.mem_or_mem h).elim ha.2 hb.2⟩ }
  refine ⟨T, fun s hs => hs, ?_⟩
  have hT : ∀ s ∈ T, s ∈ q.asIdeal.primeCompl := fun s hs => hs.2
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    exact IsLocalization.map_units (Localization.AtPrime q.asIdeal)
      (⟨s, hT s hs⟩ : q.asIdeal.primeCompl)
  · intro z
    obtain ⟨⟨x, ⟨s, hs⟩⟩, hz⟩ := IsLocalization.surj q.asIdeal.primeCompl z
    obtain ⟨e, u, he, hu, rfl⟩ := hW.2 s
    have he_q : e ∉ q.asIdeal := fun h => hs (q.asIdeal.mul_mem_right u h)
    refine ⟨⟨x * ↑hu.unit⁻¹, ⟨e, he, he_q⟩⟩, ?_⟩
    simp only at hz ⊢
    calc z * algebraMap W _ e = z * algebraMap W _ (e * u * ↑hu.unit⁻¹) := by
          rw [mul_assoc e, IsUnit.mul_val_inv, mul_one]
      _ = (z * algebraMap W _ (e * u)) * algebraMap W _ ↑hu.unit⁻¹ := by
          rw [map_mul (algebraMap W _) (e * u), mul_assoc]
      _ = algebraMap W _ x * algebraMap W _ ↑hu.unit⁻¹ := by rw [hz]
      _ = algebraMap W _ (x * ↑hu.unit⁻¹) := (map_mul _ _ _).symm
  · intro x y hxy
    obtain ⟨⟨c, hc⟩, hcxy⟩ := (IsLocalization.eq_iff_exists q.asIdeal.primeCompl _).mp hxy
    obtain ⟨e, u, he, hu, rfl⟩ := hW.2 c
    have he_q : e ∉ q.asIdeal := fun h => hc (q.asIdeal.mul_mem_right u h)
    refine ⟨⟨e, he, he_q⟩, ?_⟩
    simp only at hcxy ⊢
    have huv : u * ↑hu.unit⁻¹ = 1 := IsUnit.mul_val_inv hu
    calc e * x = e * u * x * ↑hu.unit⁻¹ := by linear_combination (-(e * x)) * huv
      _ = e * u * y * ↑hu.unit⁻¹ := by rw [hcxy]
      _ = e * y := by linear_combination (e * y) * huv
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExteriorCupCocycleExistsOfPairing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

namespace UpperTheory.Kun
variable {R : Type} [CommRing R]

private theorem sub_self_all {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have e : SimplexCategory.subinterval 0 N h = 𝟙 _ := by
    ext i
    simp [SimplexCategory.subinterval]
  unfold Sx.sub
  rw [e]
  simp

private theorem aw_conc {Q P I : Cx R} (μ : Pair Q P I) {X : Spc} {m n : ℤ} (h : m + 1 = n)
    (A : Cochain ((chains R).obj X) Q m) (B : Cochain ((chains R).obj X) P 1)
    (γ : Cochain ((chains R).obj X) I n) (hγ : μ.IsAW h A B γ)
    (hB : ∀ (p : ℕ) s hs U x, ev B (p + 1) s hs U x = 0)
    (N : ℕ) (w : ℤ) (hw : -(N : ℤ) + n = w) (U : Scheme.{0}) (x : Sx X N U) :
    ev γ N w hw U x = (N : ℤ).negOnePow • μ.mul U (w + -1) 1 w (by omega) (ev A N (w + -1) (by omega) U x)
      (ev B 0 1 (by simp) U (x.sub N 0 (by omega))) := by
  have term : ∀ (r l : ℕ) (hrl : r + l = N) (t u : ℤ) (ht : -(r : ℤ) + m = t) (hu : -(l : ℤ) + 1 = u) (hw' : t + u = w),
      μ.mul U t u w hw' (ev A r t ht U (x.sub 0 r (by omega))) (ev B l u hu U (x.sub r l (by omega))) =
        if l = 0 then μ.mul U (w + -1) 1 w (by omega) (ev A N (w + -1) (by omega) U x)
          (ev B 0 1 (by simp) U (x.sub N 0 (by omega))) else 0 := by
    intro r l hrl t u ht hu hw'
    rcases l with _ | l
    · obtain rfl : r = N := by omega
      obtain rfl : u = 1 := by simpa using hu.symm
      obtain rfl : t = w + -1 := by omega
      simp only [if_true]
      rw [sub_self_all]
    · rw [hB]
      simp
  rw [hγ N w hw U x, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
  · rw [term _ _ (by simp) _ _ rfl rfl]
    simp
  · intro i _
    rw [term _ _ (by simp <;> omega) _ _ rfl rfl, if_neg (by simp <;> omega)]
    simp

end UpperTheory.Kun

namespace UpperTheory.Kun
variable {R : Type} [CommRing R]

private theorem ev_rightShift {E : Spc} {Q : Cx R} {m n : ℤ} (h : m + 1 = n)
    (α : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    (ev (α.rightShift (-1) n (by omega)).1 p s hs U x : Sec ((sh Q).X s) U) = (ev α.1 p (s + -1) (by omega) U x : Sec (Q.X (s + -1)) U) := by
  have e : (α.rightShift (-1) n (by omega)).1.v (-(p : ℤ)) s hs =
      (show _ ⟶ (sh Q).X s from α.1.v (-(p : ℤ)) (s + -1) (by omega)) := by
    refine (Cochain.rightShift_v α.1 (-1) n (by omega) (-(p : ℤ)) s hs (s + -1) (by omega)).trans ?_
    simp [CochainComplex.shiftFunctorObjXIso]
    rfl
  unfold ev
  rw [e]
  rfl

private theorem ev_inL {E : Spc} {I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n)
    (α₂ : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (inL h α₁ α₂).1 p s hs U x =
      cc (ev α₁.1 p s hs U x) (n.negOnePow • ev α₂.1 p (s + -1) (by omega) U x) := by
  have b := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := LL I Q) (n := n)
  have e₁ : (inL h α₁ α₂).1 = α₁.1.comp (Cochain.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
      ((n.negOnePow : ℤˣ) : ℤ) • (α₂.rightShift (-1) n (by omega)).1.comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n) := rfl
  rw [e₁, (b.1 _ _ p s hs U x).1, (b.1 ((α₂.rightShift (-1) n (by omega)).1.comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n)) 0 p s hs U x).2.2.2,
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := I) (n := n)).2.2.2.2 _ α₁.1 p s hs U x,
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := sh Q) (n := n)).2.2.2.2 _ _ p s hs U x, ev_rightShift h α₂ p s hs U x]
  unfold cc
  congr 1
  rw [Units.smul_def]
  exact (map_zsmul ((((biprod.inr : sh Q ⟶ LL I Q).f s).hom.app (op U)).hom) _ _).symm

private theorem c₁_ev_inL {E : Spc} {I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n)
    (α₂ : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    c₁ (ev (inL h α₁ α₂).1 p s hs U x) = ev α₁.1 p s hs U x := by
  rw [ev_inL, c₁_cc]

private theorem c₂_ev_inL {E : Spc} {I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n)
    (α₂ : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    c₂ (ev (inL h α₁ α₂).1 p s hs U x) = n.negOnePow • ev α₂.1 p (s + -1) (by omega) U x := by
  rw [ev_inL, c₂_cc]

private theorem sub_map_sch {W : Scheme.{0}} {X : Spc} (f : X ⟶ sch.obj W) {p : ℕ} {T : Scheme.{0}} (y : Sx X p T)
    (h : p + 0 ≤ p) : (show T ⟶ W from (y.sub p 0 h).map f) = (show T ⟶ W from y.map f) := by
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality (SimplexCategory.subinterval p 0 h).op) (op T)) y

private theorem psi_read (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W) {T : Scheme.{0}} (s : ℤ)
    (f : T ⟶ W) (a : Sec ((LL I Q).X s) T) :
    Sec.res (prod.lift f (𝟙 T)) (psi W μ z T s a) =
      c₁ a + s.negOnePow • μ.mul T (s + -1) 1 s (by omega) (c₂ a) (Sec.res f z) := by
  change Sec.res (prod.lift f (𝟙 T)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ a) +
      s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)) = _
  rw [res_add, res_units, μ.nat, res_res, res_res, res_res, prod.lift_snd, prod.lift_fst, res_id, res_id]

end UpperTheory.Kun

theorem UpperTheory.exteriorCup_cocycle_exists_of_pairing :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (κ : Cocycle ((chains R).obj (sch.obj W)) P 1) {E : Spc} {m n : ℤ}
        (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n) (α₂ : Cocycle ((chains R).obj E) Q m)
        (β : Cocycle ((chains R).obj (sch.obj W ⨯ E)) I n),
        (∀ (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T),
          ev β.1 p s hs T y = Sec.res (prod.lift (show T ⟶ W from y.map prod.fst) (𝟙 T))
            (psi W μ (sg κ) T s (ev (inL h α₁ α₂).1 p s hs T (y.map prod.snd)))) →
        CohomologyClass.mk β = cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) I n (CohomologyClass.mk α₁) +
          μ.cup (sch.obj W ⨯ E) h (cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) Q m (CohomologyClass.mk α₂))
            (cpull ((chains R).map (prod.fst : sch.obj W ⨯ E ⟶ _)) P 1 (CohomologyClass.mk κ)) := by
  intro R _ W I Q P μ κ E m n h α₁ α₂ β hβ
  have hS := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R W P 0 1 2 (by norm_num) (by norm_num)
  obtain ⟨z', hz0, hz1⟩ := hS.1 (sg κ) (hS.2 κ).1
  have hκ : CohomologyClass.mk κ = CohomologyClass.mk z' := by
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub]
    refine (hS.2 (κ - z')).2.2 ⟨0, ?_⟩
    have e : sg (κ - z') = 0 := by
      rw [sg_sub]
      have e' : sg z' = sg κ := by
        have := hz0 W (𝟙 W)
        rw [res_id] at this
        exact this
      rw [e', sub_self]
    exact (map_zero ((P.d 0 1).hom.app (op W)).hom).trans e.symm
  let A : Cocycle ((chains R).obj (sch.obj W ⨯ E)) Q m :=
    zcomp (Cocycle.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))) α₂ (zero_add m)
  let B : Cocycle ((chains R).obj (sch.obj W ⨯ E)) P 1 :=
    zcomp (Cocycle.ofHom ((chains R).map (prod.fst : sch.obj W ⨯ E ⟶ _))) z' (zero_add 1)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).1 A B
  have hc := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).2 A B γ hγ
  have evA : ∀ (p : ℕ) s hs (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T), ev A.1 p s hs T y = ev α₂.1 p s hs T (y.map prod.snd) :=
    fun p s hs T y => (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := Q) (n := m)).2.2.2.1 prod.snd α₂.1 p s hs T y
  have evB : ∀ (p : ℕ) s hs (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T), ev B.1 p s hs T y = ev z'.1 p s hs T (y.map prod.fst) :=
    fun p s hs T y => (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj W) (I := P) (n := 1)).2.2.2.1 prod.fst z'.1 p s hs T y
  have hβ' : β = zcomp (Cocycle.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))) α₁ (zero_add n) + γ := by
    apply Cocycle.ext
    refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj W ⨯ E) (I := I) (n := n)).2.2.1 _ _ fun p s hs T y => ?_
    have e₁ : (zcomp (Cocycle.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))) α₁ (zero_add n) + γ).1 =
        (Cochain.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))).comp α₁.1 (zero_add n) + γ.1 := rfl
    rw [e₁, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj W ⨯ E) (I := I) (n := n)).1 _ _ p s hs T y).1,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := I) (n := n)).2.2.2.1 prod.snd α₁.1 p s hs T y,
      hβ p s hs T y, psi_read, c₁_ev_inL, c₂_ev_inL,
      aw_conc μ h A.1 B.1 γ.1 hγ (fun p s hs U x => by rw [evB]; exact hz1 p s hs U _) p s hs T y,
      evA, evB]
    congr 1
    have e₂ : ev z'.1 0 1 (by simp) T ((y.sub p 0 (by omega)).map prod.fst) = Sec.res (show T ⟶ W from y.map prod.fst) (sg κ) := by
      rw [← sub_map_sch prod.fst y (by omega)]
      exact hz0 T _
    rw [e₂]
    have hsign : s.negOnePow * n.negOnePow = (p : ℤ).negOnePow := by
      rw [← hs, Int.negOnePow_add, Int.negOnePow_neg, mul_assoc, Int.units_mul_self, mul_one]
    have key : ∀ (ε : ℤˣ) (a : Sec (Q.X (s + -1)) T) (b : Sec (P.X 1) T),
        μ.mul T (s + -1) 1 s (by omega) (ε • a) b = ε • μ.mul T (s + -1) 1 s (by omega) a b := by
      intro ε a b
      rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
    rw [key, smul_smul, hsign]
  rw [hκ, hβ', CohomologyClass.mk_add, cpre_mk, cpre_mk, cpre_mk]
  exact congrArg (fun c => _ + c) hc.symm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKummerSelmerOfFiniteExtension
section
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private theorem functionField_isAlgebraic_of_tower (k K K' : Type) [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
    [Algebra K K'] [IsScalarTower k K K'] [IsFunctionField k K] [IsFunctionField k K'] :
    Algebra.IsAlgebraic K K' := by
  have h := trdeg_add_eq k K (A := K')
  rw [trdeg_eq_one (k := k) (K := K), trdeg_eq_one (k := k) (K := K')] at h
  have hfin : Algebra.trdeg K K' < Cardinal.aleph0 :=
    lt_of_le_of_lt (h ▸ le_add_self) Cardinal.one_lt_aleph0
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hn] at h
  have hn0 : n = 0 := by
    have : ((1 + n : ℕ) : Cardinal) = ((1 : ℕ) : Cardinal) := by push_cast; exact h
    have := Nat.cast_injective this
    omega
  rw [← trdeg_eq_zero_iff, hn, hn0, Nat.cast_zero]

theorem UpperTheory.finite_kummerSelmer_of_finite_extension :
    ∀ (k K K' : Type) [Field k] [IsAlgClosed k] [Field K] [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] [IsFunctionField k K] [IsFunctionField k K'] (q : ℕ) [NeZero q], IsUnit (q : k) → FinCls q (SelAll k K' q) → FinCls q (SelAll k K q) := by
  classical
  intro k K K' _ _ _ _ _ _ _ _ _ _ q _ hq hK'
  have := functionField_isAlgebraic_of_tower k K K'
  have : Algebra.EssFiniteType k K' := essFiniteType
  have : Algebra.EssFiniteType K K' := Algebra.EssFiniteType.of_comp k K K'
  have : Module.Finite K K' := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : NeZero (q : k) := ⟨hq.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k q
  obtain ⟨T0, hT0⟩ := UpperTheory.finite_kernel_powClasses_of_primitive_root K K' q
    ⟨algebraMap k K ζ, hζ.map_of_injective (algebraMap k K).injective⟩
  obtain ⟨T', hT'⟩ := hK'
  let φ : Kˣ →* K'ˣ := Units.map (algebraMap K K' : K →* K')
  have hφ : ∀ x : Kˣ, ((φ x : K'ˣ) : K') = algebraMap K K' (x : K) := fun x => rfl
  have himg : ∀ f ∈ SelAll k K q, φ f ∈ SelAll k K' q := by
    intro f hf w
    have hw := (Place.liesOver_comap w).ord_algebraMap (f : K)
    show (q : ℤ) ∣ w.ord ((φ f : K'ˣ) : K')
    rw [hφ, hw]
    exact Dvd.dvd.mul_left (hf _) _
  let g : K'ˣ → Kˣ := fun t' =>
    if h : ∃ f ∈ SelAll k K q, ∃ u : K'ˣ, φ f = t' * u ^ q then h.choose else 1
  refine ⟨Finset.image₂ (· * ·) (T'.image g) T0, ?_⟩
  intro f hf
  obtain ⟨t', ht', u, hu⟩ := hT' (φ f) (himg f hf)
  have hex : ∃ f ∈ SelAll k K q, ∃ u : K'ˣ, φ f = t' * u ^ q := ⟨f, hf, u, hu⟩
  have hg : g t' = hex.choose := dif_pos hex
  obtain ⟨_, u0, hu0⟩ := hex.choose_spec
  set f0 := hex.choose
  have hmem : f * f0⁻¹ ∈ {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q} := by
    refine ⟨((u * u0⁻¹ : K'ˣ) : K'), ?_⟩
    rw [← hφ, map_mul, map_inv, hu, hu0]
    push_cast
    rw [mul_pow, inv_pow]
    field_simp
  obtain ⟨s, hs, w, hw⟩ := hT0 _ hmem
  refine ⟨f0 * s, Finset.mem_image₂.mpr ⟨f0, Finset.mem_image.mpr ⟨t', ht', hg⟩, s, hs, rfl⟩, w, ?_⟩
  rw [mul_assoc, ← hw, mul_comm f, mul_inv_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsCompactOpenEqBasicOpenIdempotentOfProdACF
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace LateralTheory.E.BuildCut

theorem UpperTheory.isCompact_open_eq_basicOpen_idempotent_of_prodACF :
    ∀ {W : Type} [CommRing W], ProdACF W → ∀ (V : Opens (PrimeSpectrum W)), IsCompact (V : Set (PrimeSpectrum W)) →
        ∃ e : W, IsIdempotentElem e ∧ (V : Set (PrimeSpectrum W)) = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum W)) := by
  classical
  intro W _ hW V hV
  have key : ∀ s : Finset W, ∃ e : W, IsIdempotentElem e ∧
      ∀ p : PrimeSpectrum W, ((s : Set W) ⊆ (p.asIdeal : Set W) ↔ e ∈ p.asIdeal) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, IsIdempotentElem.zero, fun p => by simp [p.asIdeal.zero_mem]⟩
    | insert a s ha ih =>
      obtain ⟨f, hf, hfs⟩ := ih
      obtain ⟨e, u, he, hu, rfl⟩ := hW.2 a
      have he' : e * e = e := he
      have hf' : f * f = f := hf
      refine ⟨e + f - e * f, ?_, fun p => ?_⟩
      · show (e + f - e * f) * (e + f - e * f) = e + f - e * f
        linear_combination (1 - f + f * f - f) * he' + (1 - e) * hf'
      · rw [Finset.coe_insert, Set.insert_subset_iff, hfs p, SetLike.mem_coe,
          Ideal.mul_unit_mem_iff_mem _ hu]
        constructor
        · rintro ⟨h1, h2⟩
          exact p.asIdeal.sub_mem (p.asIdeal.add_mem h1 h2) (p.asIdeal.mul_mem_right _ h1)
        · intro h
          have h1 : e * (e + f - e * f) = e := by linear_combination (1 - f) * he'
          have h2 : f * (e + f - e * f) = f := by linear_combination (1 - e) * hf'
          exact ⟨h1 ▸ p.asIdeal.mul_mem_left _ h, h2 ▸ p.asIdeal.mul_mem_left _ h⟩
  obtain ⟨t, ht⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hV, V.isOpen⟩
  obtain ⟨e, he, hte⟩ := key t
  refine ⟨e, he, ?_⟩
  rw [← ht]
  ext p
  simp [PrimeSpectrum.mem_zeroLocus, hte p]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsDedekindDomainAffineSectionsOfIsCurve
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem not_isField_of_curve {k : Type} [Field k] {C : Scheme.{0}} (c : C ⟶ Sp k) (hc : IsCurve c)
    (W : C.Opens) (hW : IsAffineOpen W) (hWn : (W : Set C).Nonempty) : ¬ IsField Γ(C, W) := by
  intro hF
  have h := CurveCut.CoverPf.krullDim_eq_one c hc W hW hWn
  rw [ringKrullDim_eq_zero_of_isField hF] at h
  norm_num at h

private theorem stalk_isIntegrallyClosed {k : Type} [Field k] [IsAlgClosed k] {C : Scheme.{0}} (c : C ⟶ Sp k)
    (hc : IsCurve c) (y : C) : IsIntegrallyClosed (C.presheaf.stalk y) := by
  haveI := hc.1
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by simp)
  have hne : (U : Set C).Nonempty := ⟨y, hyU⟩
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  haveI : IsIntegrallyClosed Γ(C, U) := CurveCut.CoverPf.leafNormal _ c hc U hU hne
  letI : Algebra Γ(C, U) (C.presheaf.stalk y) := C.presheaf.algebra_section_stalk ⟨y, hyU⟩
  haveI := hU.isLocalization_stalk ⟨y, hyU⟩
  exact isIntegrallyClosed_of_isLocalization _ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

theorem UpperTheory.isDedekindDomain_affine_sections_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} (c : C ⟶ Sp k), IsCurve c → (∀ W : C.Opens, IsAffineOpen W → (W : Set C).Nonempty → IsDedekindDomain Γ(C, W) ∧ ¬ IsField Γ(C, W)) ∧ ∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y) := by
  intro k _ _ C c hc
  refine ⟨fun W hW hWn => ⟨?_, not_isField_of_curve c hc W hW hWn⟩, stalk_isIntegrallyClosed c hc⟩
  exact LateralTheory.E.E4.CurveCut.CoverPf.LeafDedRing_of LateralTheory.E.E4.CurveCut.CoverPf.leafDim1
    LateralTheory.E.E4.CurveCut.CoverPf.leafNormal k c hc W hW hWn
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfIsoSquare
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem pull_bij (q : ℕ) {A B : Spc} (f : A ⟶ B) [IsIso f] (n i : ℤ) :
    Function.Bijective (fun x : Ht q B n i => (pull _ f _ _ x : Ht q A n i)) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun y => pull _ (inv f) _ _ y, fun x => ?_, fun y => ?_⟩
  · show pull _ (inv f) _ _ (pull _ f _ _ x) = x
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · show pull _ f _ _ (pull _ (inv f) _ _ y) = y
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]

private theorem pull_cup (q : ℕ) {A B : Spc} (f : A ⟶ B) {n m i j : ℤ} (a : Ht q B n i) (b : Ht q B m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b

private theorem pull_cast' (q : ℕ) {A B : Spc} (f : A ⟶ B) {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q B n i) : pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q A n i) := by
  subst hn; subst hi; rfl

theorem UpperTheory.lerayHirsch_of_iso_square :
    ∀ (q : ℕ) [NeZero q] {X X' E E' : Spc} (π : X ⟶ E) (π' : X' ⟶ E') (u : X' ⟶ X) (b : E' ⟶ E) [IsIso u] [IsIso b], u ≫ π = π' ≫ b →
        ∀ {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q X (d j) (e j)), LH q π d e c → LH q π' d e (fun j => pull _ u _ _ (c j)) := by
  intro q _ X X' E E' π π' u b _ _ w m d e c h n i
  have hP : Function.Bijective (fun (a : ∀ j, Ht q E (n - d j) (i - e j)) j =>
      (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) :=
    ⟨fun a a' haa => funext fun j => (pull_bij q b _ _).1 (congrFun haa j),
      fun y => ⟨fun j => ((pull_bij q b _ _).2 (y j)).choose,
        funext fun j => ((pull_bij q b _ _).2 (y j)).choose_spec⟩⟩
  have hc : ∀ a : ∀ j, Ht q E (n - d j) (i - e j),
      (∑ j, ((cup q (pull _ π' _ _ (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) (pull _ u _ _ (c j))).cast
        (by ring) (by ring) : Ht q X' n i)) =
      pull _ u _ _ (∑ j, ((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i)) := by
    intro a
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pull_cast', pull_cup, ← pull_comp, ← pull_comp, w]
  have hcomp := (pull_bij q u n i).comp (h n i)
  have heq : (fun y : ∀ j, Ht q E' (n - d j) (i - e j) =>
      ∑ j, ((cup q (pull _ π' _ _ (y j)) (pull _ u _ _ (c j))).cast (by ring) (by ring) : Ht q X' n i)) ∘
      (fun (a : ∀ j, Ht q E (n - d j) (i - e j)) j =>
        (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) =
      (fun x : Ht q X n i => (pull _ u _ _ x : Ht q X' n i)) ∘ (fun a : ∀ j, Ht q E (n - d j) (i - e j) =>
        ∑ j, ((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i)) :=
    funext hc
  rw [← heq] at hcomp
  exact (Function.Bijective.of_comp_iff _ hP).1 hcomp
end

