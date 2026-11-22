import Mathlib
import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0011
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0015
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0018
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LeafProdLeafLocOfLeafLevel
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem conn_mono {R : Type} [CommRing R] {F : Shv R} {c m : ℤ} (h : m ≤ c) {E E' : Spc} {f : E ⟶ E'}
    (hf : Conn R F c f) : Conn R F m f := fun n =>
  ⟨fun hn => (hf n).1 (by omega), fun hn => (hf n).2 (by omega)⟩

private theorem conn_nonpos (a9 : A9) {R : Type} [CommRing R] (F : Shv R) {m : ℤ} (h : m ≤ 0) {E E' : Spc} (f : E ⟶ E') :
    Conn R F m f := by
  intro n
  have hs := (a9 R F).1
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · haveI := hs E n (by omega)
    haveI := hs E' n (by omega)
    exact ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ y⟩⟩
  · haveI := hs E' n (by omega)
    exact fun x y _ => Subsingleton.elim x y

private theorem conn_iso {R : Type} [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E') [IsIso f] :
    Conn R F c f := by
  have hb : ∀ n, Function.Bijective (pull R f F n) := fun n =>
    Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
      fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id],
      fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩
  exact fun n => ⟨fun _ => hb n, fun _ => (hb n).1⟩

private theorem conn_congr {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {X : Scheme.{0}} {U U' : X.Opens} (e : U = U')
    (h : Conn R F c (sch.map U.ι)) : Conn R F c (sch.map U'.ι) := e ▸ h

private theorem conn_top {R : Type} [CommRing R] (F : Shv R) (c : ℤ) {X : Scheme.{0}} {U : X.Opens} (e : U = ⊤) :
    Conn R F c (sch.map U.ι) := by
  subst e
  haveI : IsIso (⊤ : X.Opens).ι := by
    first
      | infer_instance
      | (rw [← Scheme.topIso_hom]; infer_instance)
      | exact isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  exact conn_iso F c _

private theorem exists_good {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {X : Scheme.{0}} {U : X.Opens}
    (H : ∀ x : X, x ∉ U → ∀ W : X.Opens, x ∈ W → ∃ (Y : Scheme.{0}) (j : Y ⟶ X) (_ : IsOpenImmersion j),
      x ∈ Set.range j ∧ Set.range j ⊆ (W : Set X) ∧ Conn R F c (sch.map (j ⁻¹ᵁ U).ι))
    {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) :
    ∃ (O : Scheme.{0}) (o : O ⟶ Y) (_ : IsOpenImmersion o), y ∈ Set.range o ∧
      Conn R F c (sch.map ((o ≫ j) ⁻¹ᵁ U).ι) := by
  by_cases hy : j y ∈ U
  · refine ⟨_, (j ⁻¹ᵁ U).ι, inferInstance, ?_, conn_top F c ?_⟩
    · rw [Scheme.Opens.range_ι]
      exact hy
    · rw [Scheme.Hom.comp_preimage]
      exact Scheme.Opens.ι_preimage_self _
  · obtain ⟨Y', j', hj', hx, hsub, hC⟩ := H (j y) hy j.opensRange ⟨y, rfl⟩
    have hle : Set.range j' ⊆ Set.range j := hsub
    have hfac : IsOpenImmersion.lift j j' hle ≫ j = j' := IsOpenImmersion.lift_fac j j' hle
    haveI : IsOpenImmersion (IsOpenImmersion.lift j j' hle ≫ j) := by rw [hfac]; exact hj'
    refine ⟨Y', IsOpenImmersion.lift j j' hle, IsOpenImmersion.of_comp _ j, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hx
      refine ⟨z, j.isOpenEmbedding.injective ?_⟩
      rw [← hz, ← Scheme.Hom.comp_apply, hfac]
    · rw [hfac]
      exact hC

theorem UpperTheory.leafProd_leafLoc_of_leafLevel :
    LeafLevel → LeafProd → LeafLoc := by
  intro hLev hProd a1 a2 a9 R _ F c X U H
  have main : ∀ k : ℕ, ∀ {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j],
      Conn R F (min c k) (sch.map (j ⁻¹ᵁ U).ι) := by
    intro k
    induction k with
    | zero =>
      intro Y j _
      exact conn_nonpos a9 F (by simp) _
    | succ k ih =>
      intro Y j _
      have hmc : min c ((k + 1 : ℕ) : ℤ) ≤ c := min_le_left _ _
      have hm1 : min c ((k + 1 : ℕ) : ℤ) - 1 ≤ min c (k : ℤ) := by omega
      choose O o ho hyo hc using fun y : Y => exists_good H j y
      haveI := ho
      have hcomp : ∀ a, Sigma.ι O a ≫ Sigma.desc o = o a := fun a => Sigma.ι_desc _ _
      haveI hsurj : Surjective (Sigma.desc o) := ⟨fun y => by
        obtain ⟨z, hz⟩ := hyo y
        refine ⟨Sigma.ι O y z, ?_⟩
        rw [← Scheme.Hom.comp_apply, hcomp, hz]⟩
      have hdisj : ∀ a b, a ≠ b → Disjoint (Set.range (Sigma.ι O a)) (Set.range (Sigma.ι O b)) := fun a b hab => by
        have := disjoint_opensRange_sigmaι O a b hab
        rw [Set.disjoint_left]
        intro x hxa hxb
        exact (disjoint_iff_inf_le.1 this : _) ⟨hxa, hxb⟩
      have hcov : ∀ y : (∐ O : Scheme.{0}), ∃ a, y ∈ Set.range (Sigma.ι O a) := fun y => by
        obtain ⟨a, z, hz⟩ := (sigmaOpenCover O).exists_eq y
        exact ⟨a, z, hz⟩
      refine UpperTheory.connectivity_of_cech_disjoint_cover hLev a1 a2 R F _ (Sigma.desc o)
        ⟨Y, O, Sigma.ι O, inferInstance, hdisj, hcov, fun a => by rw [hcomp]; exact ho a⟩ (j ⁻¹ᵁ U) ?_ ?_
      · refine UpperTheory.connectivity_of_disjoint_open_cover hProd a1 R F _ O (Sigma.ι O) hdisj hcov _ fun a => ?_
        refine conn_congr ?_ (conn_mono hmc (hc a))
        rw [Scheme.Hom.comp_preimage, ← hcomp a, Scheme.Hom.comp_preimage]
      · rintro Z g ⟨ι', O', j', hoi, hdis', hcov', hcp⟩
        haveI := hoi
        refine UpperTheory.connectivity_of_disjoint_open_cover hProd a1 R F _ O' j' hdis' hcov' _ fun a => ?_
        haveI := hcp a
        refine conn_congr ?_ (conn_mono hm1 (ih ((j' a ≫ g) ≫ j)))
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  have hfin := main c.toNat (𝟙 X)
  have hmin : min c (c.toNat : ℤ) = c := min_eq_left (Int.self_le_toNat c)
  rw [hmin] at hfin
  exact conn_congr (Scheme.Hom.id_preimage U) hfin

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisConnectingCupPullback
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.MvLin

variable {R : Type} [CommRing R]

private noncomputable abbrev pb {E' E : Spc} (π : E' ⟶ E) {I : Cx R} {n : ℤ} (a : Cochain ((chains R).obj E) I n) :
    Cochain ((chains R).obj E') I n :=
  (Cochain.ofHom ((chains R).map π)).comp a (zero_add n)

private noncomputable abbrev pbz {E' E : Spc} (π : E' ⟶ E) {I : Cx R} {n : ℤ} (a : Cocycle ((chains R).obj E) I n) :
    Cocycle ((chains R).obj E') I n :=
  zcomp (Cocycle.ofHom ((chains R).map π)) a (zero_add n)

private theorem pb_comp {E'' E' E : Spc} (π : E'' ⟶ E') (ρ : E' ⟶ E) {I : Cx R} {n : ℤ}
    (a : Cochain ((chains R).obj E) I n) : pb (π ≫ ρ) a = pb π (pb ρ a) := by
  simp only [pb, Functor.map_comp]
  rw [Cochain.ofHom_comp]
  exact Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (zero_add n)

private theorem sub_map {E' E : Spc} (π : E' ⟶ E) {N : ℕ} {U : Scheme.{0}} (x : Sx E' N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.map π).sub j l h = (x.sub j l h).map π :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (π.naturality (SimplexCategory.subinterval j l h).op) (op U)) x).symm

private theorem ev_pb {E' E : Spc} (π : E' ⟶ E) {I : Cx R} {n : ℤ} (a : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E' p U) :
    ev (pb π a) p s h U x = ev a p s h U (x.map π) :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := I) (n := n)).2.2.2.1 π a p s h U x

private theorem aw_pb {I J K : Cx R} (μ : Pair I J K) {E' E : Spc} (π : E' ⟶ E) {n m k : ℤ} (hk : n + m = k)
    {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m} {c : Cochain ((chains R).obj E) K k}
    (h : μ.IsAW hk a b c) : μ.IsAW hk (pb π a) (pb π b) (pb π c) := by
  intro N w hw U x
  rw [ev_pb, h N w hw U (x.map π)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_pb, ev_pb, sub_map, sub_map]

private theorem aw_unique {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m} {c c' : Cochain ((chains R).obj E) K k}
    (h : μ.IsAW hk a b c) (h' : μ.IsAW hk a b c') : c = c' :=
  ((GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ hk).1 a b).unique h h'

private theorem aw_zero {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (a : Cochain ((chains R).obj E) I n) : μ.IsAW hk a (0 : Cochain ((chains R).obj E) J m) 0 := by
  obtain ⟨z, hz, -⟩ := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ hk).1 a (0 : Cochain ((chains R).obj E) J m)
  have h2 := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ hk).2.2 a 0 0 z z hz hz
  rw [add_zero] at h2
  have h3 : z + z = z := aw_unique μ hk h2 hz
  have h4 : z = 0 := by simpa using h3
  exact h4 ▸ hz

private theorem aw_delta {I J K : Cx R} (μ : Pair I J K) {E' E : Spc} (π : E' ⟶ E) {n m : ℤ}
    {a : Cochain ((chains R).obj E') I n} {z : Cocycle ((chains R).obj E) I (n + 1)} {η : Cocycle ((chains R).obj E) J m}
    {a' : Cochain ((chains R).obj E') K (n + m)} {z' : Cochain ((chains R).obj E) K (n + m + 1)}
    (hk : n + 1 + m = n + m + 1) (ha : δ n (n + 1) a = pb π z.1) (h1 : μ.IsAW rfl a (pbz π η).1 a')
    (h2 : μ.IsAW hk z.1 η.1 z') : δ (n + m) (n + m + 1) a' = pb π z' := by
  have h3 : μ.IsAW hk (δ n (n + 1) a) (pbz π η).1 (pb π z') := ha ▸ aw_pb μ π hk h2
  have h4 : μ.IsAW (by omega : n + (m + 1) = n + m + 1) a (δ m (m + 1) (pbz π η).1) 0 := by
    rw [Cocycle.δ_eq_zero]
    exact aw_zero μ _ a
  have h5 := GlobalTheory.T.alexanderWhitney_cup_leibniz_etale R μ rfl a (pbz π η).1 a' (pb π z') 0 h1 h3 h4
  simpa using h5

private theorem mv_core {I J K : Cx R} (μ : Pair I J K) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) {n m : ℤ}
    (γ : Cocycle ((chains R).obj (pullback f g)) I n) (ζ : Cocycle ((chains R).obj E) I (n + 1))
    (α : Cochain ((chains R).obj U) I n) (β : Cochain ((chains R).obj V) I n)
    (η : Cocycle ((chains R).obj E) J m)
    (hγ : pb (pullback.fst f g) α - pb (pullback.snd f g) β = γ.1)
    (hα : δ n (n + 1) α = pb f ζ.1) (hβ : δ n (n + 1) β = pb g ζ.1) (hk : n + 1 + m = n + m + 1) :
    ∃ (γ' : Cocycle ((chains R).obj (pullback f g)) K (n + m)) (ζ' : Cocycle ((chains R).obj E) K (n + m + 1))
      (α' : Cochain ((chains R).obj U) K (n + m)) (β' : Cochain ((chains R).obj V) K (n + m)),
      μ.IsAW rfl γ.1 (pbz (pullback.fst f g ≫ f) η).1 γ'.1 ∧ μ.IsAW hk ζ.1 η.1 ζ'.1 ∧
      pb (pullback.fst f g) α' - pb (pullback.snd f g) β' = γ'.1 ∧
      δ (n + m) (n + m + 1) α' = pb f ζ'.1 ∧ δ (n + m) (n + m + 1) β' = pb g ζ'.1 := by
  obtain ⟨γ', hγ'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ rfl).1 γ (pbz (pullback.fst f g ≫ f) η)
  obtain ⟨ζ', hζ'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ hk).1 ζ η
  obtain ⟨α', hα', -⟩ := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ rfl).1 α (pbz f η).1
  obtain ⟨β', hβ', -⟩ := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ rfl).1 β (pbz g η).1
  refine ⟨γ', ζ', α', β', hγ', hζ', ?_, aw_delta μ f hk hα hα' hζ', aw_delta μ g hk hβ hβ' hζ'⟩
  have e1 : pb (pullback.fst f g) (pbz f η).1 = (pbz (pullback.fst f g ≫ f) η).1 := (pb_comp _ _ _).symm
  have e2 : pb (pullback.snd f g) (pbz g η).1 = (pbz (pullback.fst f g ≫ f) η).1 :=
    (pb_comp _ _ _).symm.trans (by rw [pullback.condition]; rfl)
  have a1 := aw_pb μ (pullback.fst f g) rfl hα'
  have a2 := aw_pb μ (pullback.snd f g) rfl hβ'
  rw [e1] at a1
  rw [e2] at a2
  have a3 := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ rfl).2.1 _ _ _ _ _ hγ' a2
  have e3 : γ.1 + pb (pullback.snd f g) β = pb (pullback.fst f g) α := by rw [← hγ, sub_add_cancel]
  rw [e3] at a3
  have e4 := aw_unique μ rfl a1 a3
  rw [e4, add_sub_cancel_right]

private theorem cast_cup (q : ℕ) {E : Spc} {n m k i j : ℤ} (hk : n + m = k) (a : Ht q E n i) (b : Ht q E m j) :
    (cup q a b).cast hk rfl = (twPair q i j).cup E hk a b := by
  subst hk
  rfl

end UpperTheory.MvLin

open UpperTheory.MvLin in
theorem UpperTheory.mayerVietorisConnecting_cup_pullback :
    ∀ (q : ℕ) [NeZero q] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 (ZMod q) f g → ∀ (n m i j : ℤ) (c : Ht q (pullback f g) n i)
        (x : Ht q E (n + 1) i) (y : Ht q E m j), IsMVd f g (tw q i) n c x →
        IsMVd f g (tw q (i + j)) (n + m) (cup q c (pull _ (pullback.fst f g ≫ f) _ _ y)) ((cup q x y).cast (by ring) rfl) := by
  intro q _ U V E f g _ n m i j c x y h
  obtain ⟨γ, ζ, α, β, rfl, rfl, hγ, hα, hβ⟩ := h
  obtain ⟨η, rfl⟩ := y.mk_surjective
  have hk : n + 1 + m = n + m + 1 := by ring
  obtain ⟨γ', ζ', α', β', h1, h2, h3, h4, h5⟩ := mv_core (twPair q i j) f g γ ζ α β η hγ hα hβ hk
  refine ⟨γ', ζ', α', β', ?_, ?_, h3, h4, h5⟩
  · exact ((GlobalTheory.T.cup_eq_class_of_isAW _ (twPair q i j) rfl).2 γ _ γ' h1).symm
  · rw [cast_cup q hk]
    exact ((GlobalTheory.T.cup_eq_class_of_isAW _ (twPair q i j) hk).2 ζ η ζ' h2).symm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MemPullbackImageIffFactorsThroughOpen
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private noncomputable abbrev evF (p : ℕ) (W : Scheme.{0}) : Spc ⥤ Type :=
  ((evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk p))) ⋙
    ((evaluation Scheme.{0}ᵒᵖ Type).obj (op W))

theorem UpperTheory.mem_pullbackImage_iff_factors_through_open :
    ∀ {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (p : ℕ) (W : Scheme.{0}) (z : Sx E p W), ((Sub.img (E := E) (pullback.fst π (sch.map U.ι))).mem p W z ↔ ∃ w : W ⟶ U.toScheme, w ≫ U.ι = under π z) ∧ (∀ (V : Scheme.{0}) (g : V ⟶ W), under π (z.res g) = g ≫ under π z) ∧ ∀ (r : ℕ) (θ : SimplexCategory.mk r ⟶ SimplexCategory.mk p), under π (z.along θ) = under π z := by
  intro X U E π p W z
  have hpb : IsPullback ((evF p W).map (pullback.fst π (sch.map U.ι)))
      ((evF p W).map (pullback.snd π (sch.map U.ι))) ((evF p W).map π)
      ((evF p W).map (sch.map U.ι)) := (IsPullback.of_hasPullback π (sch.map U.ι)).map (evF p W)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(evF p W).map (pullback.snd π (sch.map U.ι)) y, ?_⟩
    exact (ConcreteCategory.congr_hom hpb.w y).symm
  · rintro ⟨w, hw⟩
    obtain ⟨y, hy, -⟩ := Types.exists_of_isPullback hpb z (show Sx (sch.obj U.toScheme) p W from w) hw.symm
    exact ⟨y, hy⟩
  · intro V g
    exact ConcreteCategory.congr_hom ((π.app (op (SimplexCategory.mk p))).naturality g.op) z
  · intro r θ
    exact congrFun (congrArg (fun t => t.app (op W)) (π.naturality θ.op)) z
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.NerveAffineRepresentable
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory.LevelRep

noncomputable section

private abbrev Smp (D : Type) [CommRing D] (d p : ℕ) (A : Type) [CommRing A] : Type :=
  {x : Fin (p + 1) → (Vec D d).obj A // ∀ i j, (Vec D d).rel (x i) (x j)}

variable {D : Type} [CommRing D] {d p : ℕ}

private theorem rel_iff {A : Type} [CommRing A] {x y : (Vec D d).obj A} :
    (Vec D d).rel x y ↔ x.1.1 = y.1.1 ∧ ∃ u : Aˣ, x.1.2 = fun j => (u : A) * y.1.2 j := Iff.rfl

private def smpMap {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (x : Smp D d p A) : Smp D d p A' :=
  ⟨fun i => (Vec D d).map f (x.1 i), fun i j => (Vec D d).map_rel f (x.2 i j)⟩

private theorem scalar_unique {A : Type} [CommRing A] {N : ℕ} {v : Fin N → A}
    (hv : Ideal.span (Set.range v) = ⊤) {a b : A} (h : ∀ j, a * v j = b * v j) : a = b := by
  have key : ∀ y ∈ Ideal.span (Set.range v), a * y = b * y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact h j
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, mul_add, hy, hz]
    | smul c y _ hy =>
      simp only [smul_eq_mul]
      rw [mul_left_comm, hy, mul_left_comm]
  have h1 := key 1 (by rw [hv]; trivial)
  simpa using h1

private theorem exists_unit {A : Type} [CommRing A] (x : Smp D d p A) (k : Fin p) :
    ∃ u : Aˣ, (x.1 k.succ).1.2 = fun j => (u : A) * (x.1 0).1.2 j :=
  (rel_iff.1 (x.2 k.succ 0)).2

private def uOf {A : Type} [CommRing A] (x : Smp D d p A) (k : Fin p) : Aˣ :=
  Classical.choose (exists_unit x k)

private theorem uOf_spec {A : Type} [CommRing A] (x : Smp D d p A) (k : Fin p) (j : Fin d) :
    (x.1 k.succ).1.2 j = (uOf x k : A) * (x.1 0).1.2 j :=
  congrFun (Classical.choose_spec (exists_unit x k)) j

private def toRing {A : Type} [CommRing A] (x : Smp D d p A) : MvPolynomial (Fin d ⊕ Fin p) D →+* A :=
  MvPolynomial.eval₂Hom (x.1 0).1.1 (Sum.elim (x.1 0).1.2 fun k => (uOf x k : A))

private theorem toRing_C {A : Type} [CommRing A] (x : Smp D d p A) (c : D) :
    toRing x (MvPolynomial.C c) = (x.1 0).1.1 c := by
  simp [toRing]

private theorem toRing_inl {A : Type} [CommRing A] (x : Smp D d p A) (j : Fin d) :
    toRing x (MvPolynomial.X (Sum.inl j)) = (x.1 0).1.2 j := by
  simp [toRing]

private theorem toRing_inr {A : Type} [CommRing A] (x : Smp D d p A) (k : Fin p) :
    toRing x (MvPolynomial.X (Sum.inr k)) = (uOf x k : A) := by
  simp [toRing]

private theorem toRing_map {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (x : Smp D d p A) :
    toRing (smpMap f x) = f.comp (toRing x) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
  · rw [toRing_C, RingHom.comp_apply, toRing_C]
    rfl
  · rcases j with j | k
    · rw [toRing_inl, RingHom.comp_apply, toRing_inl]
      rfl
    · rw [toRing_inr, RingHom.comp_apply, toRing_inr]
      refine scalar_unique ((smpMap f x).1 0).2 fun j => ?_
      rw [← uOf_spec]
      change f ((x.1 k.succ).1.2 j) = f (uOf x k : A) * f ((x.1 0).1.2 j)
      rw [uOf_spec, map_mul]

private def Jd (D : Type) [CommRing D] (d p : ℕ) : Ideal (MvPolynomial (Fin d ⊕ Fin p) D) :=
  Ideal.span (Set.range fun j : Fin d => (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin d ⊕ Fin p) D)) *
    Ideal.span {∏ k : Fin p, (MvPolynomial.X (Sum.inr k) : MvPolynomial (Fin d ⊕ Fin p) D)}

private theorem map_Jd_iff {A : Type} [CommRing A] (ξ : MvPolynomial (Fin d ⊕ Fin p) D →+* A) :
    (Jd D d p).map ξ = ⊤ ↔
      Ideal.span (Set.range fun j : Fin d => ξ (MvPolynomial.X (Sum.inl j))) = ⊤ ∧
        ∀ k : Fin p, IsUnit (ξ (MvPolynomial.X (Sum.inr k))) := by
  rw [Jd, Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton, ← Set.range_comp, map_prod]
  change Ideal.span (Set.range fun j : Fin d => ξ (MvPolynomial.X (Sum.inl j))) * _ = ⊤ ↔ _
  constructor
  · intro h
    refine ⟨top_le_iff.1 (h ▸ Ideal.mul_le_left), fun k => ?_⟩
    have h2 : Ideal.span {∏ k : Fin p, ξ (MvPolynomial.X (Sum.inr k))} = ⊤ :=
      top_le_iff.1 (h ▸ Ideal.mul_le_right)
    rw [Ideal.span_singleton_eq_top] at h2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)] at h2
    exact isUnit_of_mul_isUnit_left h2
  · rintro ⟨h1, h2⟩
    have h3 : IsUnit (∏ k : Fin p, ξ (MvPolynomial.X (Sum.inr k))) := by
      refine Finset.prod_induction _ IsUnit (fun a b => IsUnit.mul) isUnit_one fun k _ => h2 k
    rw [h1, Ideal.span_singleton_eq_top.2 h3, Ideal.top_mul]

private theorem map_toRing {A : Type} [CommRing A] (x : Smp D d p A) : (Jd D d p).map (toRing x) = ⊤ := by
  refine (map_Jd_iff _).2 ⟨?_, fun k => ?_⟩
  · simp only [toRing_inl]
    exact (x.1 0).2
  · rw [toRing_inr]
    exact (uOf x k).isUnit

private theorem toRing_injective {A : Type} [CommRing A] {x y : Smp D d p A} (h : toRing x = toRing y) : x = y := by
  have h0 : x.1 0 = y.1 0 := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · ext c
      rw [← toRing_C, ← toRing_C, h]
    · funext j
      rw [← toRing_inl, ← toRing_inl, h]
  refine Subtype.ext (funext fun i => ?_)
  refine Fin.cases h0 (fun k => ?_) i
  have hr : (x.1 k.succ).1.1 = (y.1 k.succ).1.1 := by
    rw [(rel_iff.1 (x.2 k.succ 0)).1, (rel_iff.1 (y.2 k.succ 0)).1, h0]
  refine Subtype.ext (Prod.ext hr (funext fun j => ?_))
  have hu : (uOf x k : A) = uOf y k := by
    rw [← toRing_inr, ← toRing_inr, h]
  rw [uOf_spec, uOf_spec, hu, h0]

private def wOf {A : Type} [CommRing A] (w : Fin p → Aˣ) (i : Fin (p + 1)) : Aˣ :=
  Fin.cases 1 w i

private def ofRing {A : Type} [CommRing A] (ξ : MvPolynomial (Fin d ⊕ Fin p) D →+* A)
    (h1 : Ideal.span (Set.range fun j : Fin d => ξ (MvPolynomial.X (Sum.inl j))) = ⊤) (w : Fin p → Aˣ) :
    Smp D d p A :=
  ⟨fun i => ⟨(ξ.comp MvPolynomial.C, fun j => ξ (MvPolynomial.X (Sum.inl j)) * (wOf w i : A)),
      span_mul_unit _ (wOf w i).isUnit h1⟩,
    fun i j => rel_iff.2 ⟨rfl, wOf w i * (wOf w j)⁻¹, funext fun l => by
      change ξ (MvPolynomial.X (Sum.inl l)) * (wOf w i : A) =
        ((wOf w i * (wOf w j)⁻¹ : Aˣ) : A) * (ξ (MvPolynomial.X (Sum.inl l)) * (wOf w j : A))
      rw [Units.val_mul, mul_comm (ξ _) (wOf w j : A), mul_assoc, ← mul_assoc _ (wOf w j : A), Units.inv_mul, one_mul,
        mul_comm]⟩⟩

private theorem toRing_ofRing {A : Type} [CommRing A] (ξ : MvPolynomial (Fin d ⊕ Fin p) D →+* A)
    (h1 : Ideal.span (Set.range fun j : Fin d => ξ (MvPolynomial.X (Sum.inl j))) = ⊤) (w : Fin p → Aˣ)
    (hw : ∀ k, (w k : A) = ξ (MvPolynomial.X (Sum.inr k))) :
    toRing (ofRing ξ h1 w) = ξ := by
  have h0 : ∀ j, ((ofRing ξ h1 w).1 0).1.2 j = ξ (MvPolynomial.X (Sum.inl j)) := fun j => by
    change ξ (MvPolynomial.X (Sum.inl j)) * (wOf w 0 : A) = _
    simp [wOf]
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
  · rw [toRing_C]
    rfl
  · rcases j with j | k
    · rw [toRing_inl, h0]
    · rw [toRing_inr, ← hw]
      refine scalar_unique ((ofRing ξ h1 w).1 0).2 fun j => ?_
      rw [← uOf_spec, h0, mul_comm]
      change ξ (MvPolynomial.X (Sum.inl j)) * (wOf w k.succ : A) = _
      simp [wOf]

private theorem existsUnique_toRing {A : Type} [CommRing A] (ξ : MvPolynomial (Fin d ⊕ Fin p) D →+* A)
    (h : (Jd D d p).map ξ = ⊤) : ∃! x : Smp D d p A, toRing x = ξ := by
  obtain ⟨h1, h2⟩ := (map_Jd_iff ξ).1 h
  refine ⟨ofRing ξ h1 fun k => (h2 k).unit, toRing_ofRing ξ h1 _ fun k => (h2 k).unit_spec, fun y hy => ?_⟩
  exact toRing_injective (hy.trans (toRing_ofRing ξ h1 _ fun k => (h2 k).unit_spec).symm)

end

end UpperTheory.LevelRep

open UpperTheory.LevelRep in
theorem UpperTheory.nerve_affine_representable :
    ∀ (D : Type) [CommRing D] (d : ℕ) (n : SimplexCategoryᵒᵖ), ∃ (Y : Scheme.{0}) (_ : D →+* Γ(Y, ⊤)) (φ : (CN (Vec D d)).obj n ⟶ yoneda.obj Y), ∀ T : Scheme.{0}, IsAffine T → Function.Bijective (φ.app (op T)) := by
  intro D _ d n
  obtain ⟨U, hU⟩ := exists_compl (Jd D d n.unop.len)
  obtain ⟨φ, -, hφ⟩ := UpperTheory.represented_by_units (Jd D d n.unop.len) U hU ((CN (Vec D d)).obj n)
    (fun T x => toRing (D := D) (d := d) (p := n.unop.len) x)
    (fun f x => toRing_map f.appTop.hom x) (fun T x => map_toRing x)
    (fun T ξ h => existsUnique_toRing ξ h)
  exact ⟨U, U.ι.appTop.hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin d ⊕ Fin n.unop.len) D))).inv.hom.comp
    MvPolynomial.C), φ, hφ⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.PsiCommDifferentialOfCocycle
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

private theorem map_units {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (ε : ℤˣ) (x : Sec F U) :
    Sec.map φ (ε • x) = ε • Sec.map φ x := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

private theorem map_add' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y :=
  map_add _ _ _

private theorem mul_mid {R : Type} [CommRing R] {I Q P : Cx R} (μ : Pair Q P I) (U : Scheme.{0}) (k m m' w : ℤ) (e : m = m')
    (h : m + 1 = w) (h' : m' + 1 = w) (A : Sec (Q.X k) U) (B : Sec (P.X 1) U) :
    μ.mul U m 1 w h (Sec.map (Q.d k m) A) B = μ.mul U m' 1 w h' (Sec.map (Q.d k m') A) B := by
  subst e
  rfl

theorem UpperTheory.psi_comm_differential_of_cocycle :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W), Sec.map (P.d 1 2) z = 0 →
        ∀ (T : Scheme.{0}) (s t : ℤ) (a : Sec ((LL I Q).X s) T),
          Sec.map (I.d s t) (psi W μ z T s a) = psi W μ z T t (Sec.map ((LL I Q).d s t) a) := by
  intro R _ W I Q P μ z hz T s t a
  by_cases hst : s + 1 = t
  · subst hst
    have hB : Sec.map (P.d 1 (1 + 1)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z) = 0 := by
      rw [← res_map]
      have h2 : Sec.map (P.d 1 (1 + 1)) z = 0 := hz
      rw [h2]
      exact map_zero _
    have hL := μ.leibniz (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a))
      (Sec.res (prod.fst : W ⨯ T ⟶ W) z)
    rw [hB, map_zero, smul_zero, add_zero,
      mul_mid μ (W ⨯ T) (s + -1) (s + -1 + 1) (s + 1 + -1) (s + 1) (by omega) (by omega) (by omega)] at hL
    change Sec.map (I.d s (s + 1)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ a) +
        s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)) =
      Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ (Sec.map ((LL I Q).d s (s + 1)) a)) +
        (s + 1).negOnePow • μ.mul (W ⨯ T) (s + 1 + -1) 1 (s + 1) (by omega)
          (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ (Sec.map ((LL I Q).d s (s + 1)) a))) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)
    rw [map_add', map_units, hL, c₁_d, c₂_d, res_map, Int.negOnePow_succ]
    congr 1
    have hn : Sec.res (prod.snd : W ⨯ T ⟶ T) (- Sec.map (Q.d (s + -1) (s + 1 + -1)) (c₂ a)) =
        - Sec.map (Q.d (s + -1) (s + 1 + -1)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) := by
      rw [← res_map]
      exact map_neg _ _
    rw [hn, map_neg, LinearMap.neg_apply, smul_neg, Units.neg_smul, neg_neg]
  · have h1 : I.d s t = 0 := I.shape _ _ hst
    have h2 : (LL I Q).d s t = 0 := (LL I Q).shape _ _ hst
    rw [h1, h2, map_zeroS, map_zeroS, map_zero]
end

