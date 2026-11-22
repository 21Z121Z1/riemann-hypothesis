import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0454
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0119
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0591
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CorrespondenceDiagonal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartExtensionHolds
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht

noncomputable section

namespace GlobalTheory.LocM.Cht

theorem isFractionRing_ball (C : Type) [NormedField C] [IsUltrametricDist C] : IsFractionRing (intO C) C := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  by_cases h : ‖z‖ ≤ 1
  · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · exact ⟨1, ⟨z⁻¹, show ‖z⁻¹‖ ≤ 1 by rw [norm_inv]; exact inv_le_one_of_one_le₀ (le_of_not_ge h)⟩,
      by rw [map_one, one_div]; exact (inv_inv z).symm⟩

section Ext

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}

theorem exists_pt_of_range (i : Idx H p) (k : Type) [Field k] (x : Sp k ⟶ (Y i).X)
    (hx : Set.range x ⊆ Set.range (Y i).j) :
    ∃ (f : i.c.F →+* k) (y : Sp k ⟶ (Xo i.l).XF i.c), y ≫ pullback.snd _ _ = spMap f ∧ y ≫ (Y i).j = x := by
  have := (Y i).jQ_open
  let g : i.c.V W →+* k := (Spec.preimage (x ≫ (Y i).s)).hom
  have hg : spMap g = x ≫ (Y i).s := Spec.map_preimage _
  have hinj : Function.Injective g := by
    obtain ⟨q⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
    obtain ⟨y₀, hy₀⟩ := hx ⟨q, rfl⟩
    have e1 : (spMap g) q = (pullback.snd _ _ ≫ spMap (i.c.V W).subtype) y₀ := by
      rw [hg, ← Model.j_s, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy₀]
    rw [Scheme.Hom.comp_apply] at e1
    obtain ⟨r, hr⟩ : ∃ r : PrimeSpectrum i.c.F, (spMap g) q = (spMap (i.c.V W).subtype) r := ⟨_, e1⟩
    have e2 := congrArg PrimeSpectrum.asIdeal hr
    change Ideal.comap g q.asIdeal = Ideal.comap (i.c.V W).subtype r.asIdeal at e2
    rw [@Ideal.eq_bot_of_prime _ _ _ q.2, Ideal.eq_bot_of_prime (K := i.c.F) r.asIdeal,
      Ideal.comap_bot_of_injective _ (i.c.V W).subtype_injective] at e2
    exact (RingHom.injective_iff_ker_eq_bot g).2 e2
  let f : i.c.F →+* k := IsFractionRing.lift hinj
  have hf : f.comp (i.c.V W).subtype = g := RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a
  have hpre : IsPreimmersion (spMap (i.c.V W).subtype) :=
    IsPreimmersion.of_isLocalization (R := i.c.V W) (S := i.c.F) (nonZeroDivisors _)
  let q : Sp k ⟶ pullback (Y i).s (spMap (i.c.V W).subtype) :=
    pullback.lift x (spMap f) (by rw [← hg, ← hf, spMap_comp])
  have hq : q ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hr : Set.range q ⊆ Set.range (Y i).jQ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := hx ⟨z, rfl⟩
    refine ⟨y, (pullback.fst (Y i).s (spMap (i.c.V W).subtype)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq]
    exact hy
  refine ⟨f, IsOpenImmersion.lift _ q hr, ?_, ?_⟩
  · rw [← (Y i).jQ_over, IsOpenImmersion.lift_fac_assoc]
    exact pullback.lift_snd _ _ _
  · rw [Model.j, IsOpenImmersion.lift_fac_assoc, hq]

theorem exists_ptAt {i₀ : Idx H p} (Z : Mdl Y i₀) (C : SCF p) (z : Sp ↥(intO ↥C.S) ⟶ Z.X)
    (hz : Set.range (spMap (intO ↥C.S).subtype ≫ z) ⊆ Z.opn) : ∃ y : PtAt Z C, y.z = z := by
  let alg : Z.i.c.V W →+* ↥(intO ↥C.S) := (Spec.preimage (z ≫ Z.s)).hom
  have halg : spMap alg = z ≫ Z.s := Spec.map_preimage _
  obtain ⟨f, y, hy₁, hy₂⟩ := exists_pt_of_range (Y := Y) Z.i ↥C.S (spMap (intO ↥C.S).subtype ≫ z ≫ Z.π) (by
    rintro _ ⟨q, rfl⟩
    have := hz ⟨q, rfl⟩
    rw [← Category.assoc]
    exact this)
  have hs : z ≫ Z.π ≫ (Y Z.i).s = spMap alg := by rw [halg, Z.π_s]
  have compat : (intO ↥C.S).subtype.comp alg = f.comp (Z.i.c.V W).subtype := by
    have h : spMap ((intO ↥C.S).subtype.comp alg) = spMap (f.comp (Z.i.c.V W).subtype) := by
      rw [spMap_comp, spMap_comp, ← hs, ← hy₁, Category.assoc, ← Model.j_s, ← Category.assoc y, hy₂]
      simp only [Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  exact ⟨⟨⟨alg, f, compat, y, hy₁, z ≫ Z.π, hs, by rw [hy₂]⟩, z, rfl⟩, rfl⟩

theorem exists_ptAt_gen {i₀ : Idx H p} (Z : Mdl Y i₀) (C : SCF p) (w : Sp ↥C.S ⟶ Z.X)
    (alg : Z.i.c.V W →+* ↥(intO ↥C.S)) (hw : Set.range w ⊆ Z.opn)
    (hws : w ≫ Z.s = spMap ((intO ↥C.S).subtype.comp alg)) : ∃ y : PtAt Z C, y.gen = w := by
  have : IsProper Z.s := projProper _ _ Z.s ⟨Z.n, Z.I.subschemeι, inferInstance, rfl⟩
  have := isFractionRing_ball ↥C.S
  have hE : ValuativeCriterion.Existence Z.s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Z.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact : MorphismProperty Scheme) Z.s).1
  let S : ValuativeCommSq Z.s :=
    { R := ↥(intO ↥C.S)
      K := ↥C.S
      i₁ := w
      i₂ := spMap alg
      commSq := ⟨by rw [hws, spMap_comp]; rfl⟩ }
  obtain ⟨⟨l⟩⟩ := hE S
  have hl : spMap (intO ↥C.S).subtype ≫ l.l = w := l.fac_left
  obtain ⟨y, hy⟩ := exists_ptAt Z C l.l (by rw [hl]; exact hw)
  exact ⟨y, by rw [PtAt.gen, hy, hl]⟩

theorem extendSt : ExtendSt := by
  intro E _ _ _ H Dw Xo p W Y i₀
  exact ⟨fun i k _ x hx => exists_pt_of_range i k x hx, fun Z C z hz => exists_ptAt Z C z hz,
    fun Z C w alg hw hws => exists_ptAt_gen Z C w alg hw hws⟩

end Ext

end GlobalTheory.LocM.Cht
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM.FrameBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_tangent_module {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] (x : Sp S ⟶ X) :
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module S N) (v : N → (Sp (DualNumber S) ⟶ t.G.left))
      (ρ : 𝓞 E →+* Module.End S N), Function.Injective v ∧ (∀ w, IsTanAtG t x w ↔ w ∈ Set.range v) ∧
      (∀ (n : ℕ) (b : Fin n → N) (a : Fin n → S) w,
        IsCombAtG t x (fun i => v (b i)) a w ↔ w = v (∑ i, a i • b i)) ∧
      (∀ a m, v (ρ a m) = v m ≫ (t.act.act a).left) ∧ ∀ (s : S) m, v (s • m) = spMap (epsMul s) ≫ v m := by
  have := t.semi.comm
  refine ⟨TanMod.TanSp x t.G, inferInstance, inferInstance, fun m => m.pt.left, TanMod.TanSp.act x t.act,
    fun m n h => TanMod.TanSp.ext (Over.OverMorphism.ext h), fun w => ⟨fun h => ?_, ?_⟩, fun n b a w => ⟨?_, ?_⟩,
    fun a m => rfl, fun s m => rfl⟩
  · exact ⟨TanMod.TanSp.mk (Over.homMk w h.1) (TanMod.smT_zero_of x _ h.2), rfl⟩
  · rintro ⟨m, rfl⟩
    exact ⟨Over.w m.pt, TanMod.unit_of_smT_zero x _ m.tan⟩
  · rintro ⟨u, hu, rfl⟩
    have : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
    subst this
    rw [List.prod_ofFn, ← TanMod.TanSp.pt_sum]
  · rintro rfl
    exact ⟨fun i => (a i • b i).pt, fun i => rfl, by rw [List.prod_ofFn, ← TanMod.TanSp.pt_sum]⟩

theorem eigBasis_iff {Dw : Datum H} {l : Level H} (c : Coeff l) {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S]
    (f : c.F →+* S) (x : Sp S ⟶ X) (u : Vecs Dw t S) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (ht : ∀ τ i, IsTanAtG t x (u τ i))
    (he : ∀ τ i (a : 𝓞 E), u τ i ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ u τ i) :
    (∀ τ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ w) →
      ∃! a : Fin (Dw.mult τ) → S, IsCombAtG t x (u τ) a w) ↔
    ∀ w, IsTanAtG t x w → ∃! a : Fin g → S, IsCombAtG t x (fun j => u (e j).1 (e j).2) a w := by
  let _ : Algebra c.F S := f.toAlgebra
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, hρ, hsm⟩ := exists_tangent_module t x
  choose b hb using fun τ i => (htan (u τ i)).1 (ht τ i)
  obtain rfl : u = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  let M : (E →+* ℂ) → Submodule S N := fun τ =>
    ⨅ a : 𝓞 E, Module.End.eigenspace (ρ a) (f (embK c τ a))
  have hM : ∀ τ n, n ∈ M τ ↔ ∀ a, ρ a n = f (embK c τ a) • n := by
    intro τ n
    simp only [M, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hE : ∀ τ n, (∀ a : 𝓞 E, v n ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ v n) ↔ n ∈ M τ := by
    intro τ n
    rw [hM]
    refine forall_congr' fun a => ?_
    rw [← hρ, ← hsm, hinj.eq_iff]
  have hs : ∀ n : N, ∃! f : (E →+* ℂ) → N, (∀ τ, f τ ∈ M τ) ∧ ∑ τ, f τ = n := by
    intro n
    simp only [hM]
    exact GlobalTheory.Frames.existsUnique_eigen_sum E H l c S N ρ n
  have hmain := GlobalTheory.Frames.basis_iff_of_split (fun τ => Dw.mult τ) M hs b (fun τ i => (hE τ _).1 (he τ i)) g e
  have hT : ∀ n, IsTanAtG t x (v n) := fun n => (htan _).2 ⟨n, rfl⟩
  have hC : ∀ (k : ℕ) (b : Fin k → N) (a : Fin k → S) (n : N),
      IsCombAtG t x (fun i => v (b i)) a (v n) ↔ n = ∑ i, a i • b i := by
    intro k b a n
    rw [hcomb, hinj.eq_iff]
  constructor
  · intro h w hw
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.1 (fun τ n hn => by
      have h2 := h τ (v n) (hT n) ((hE τ n).2 hn)
      simpa only [hC] using h2) n
    simpa only [hC] using h1
  · intro h τ w hw hew
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.2 (fun n => by
      have h2 := h (v n) (hT n)
      simpa only [hC] using h2) τ n ((hE τ n).1 hew)
    simpa only [hC] using h1

theorem lieBasis_iff {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] (x : Sp S ⟶ X) (G' : Over (Sp S)) [GrpObj G']
    (φ : G'.left ⟶ t.G.left) (hp : IsGrpPullback G' t.G x φ) :
    (∀ w : (Sp (DualNumber S) ⟶ t.G.left), IsTanAtG t x w → ∃ v : epsR S ⟶ G', v.left ≫ φ = w) ∧
    ∀ (n : ℕ) (v : Fin n → (epsR S ⟶ G')), IsLieBasis v ↔ ((∀ i, IsTanAtG t x ((v i).left ≫ φ)) ∧
      ∀ w, IsTanAtG t x w → ∃! a : Fin n → S, IsCombAtG t x (fun i => (v i).left ≫ φ) a w) := by
  let up : ∀ w : Sp (DualNumber S) ⟶ t.G.left,
      w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x → (epsR S ⟶ G') :=
    fun w h => Over.homMk (hp.1.lift w _ h) (hp.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => hp.1.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ G'}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (hp.1.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ x) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have e : η[G'].left ≫ φ = (1 : Over.mk x ⟶ t.G).left := by
    have e₁ : (1 : 𝟙_ (Over (Sp S)) ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [← e₁, one]
    exact congrArg (· ≫ (η[t.G]).left) (Category.id_comp x)
  have zs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have tan : ∀ w : epsR S ⟶ G', IsTangent w ↔ IsTanAtG t x (w.left ≫ φ) := fun w => by
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => hp.1.hom_ext ?_ ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
    · refine (Category.assoc _ _ _).trans ?_
      rw [Over.w w, Over.w η[G']]
      exact zs
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x ⟶ t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) w,
      IsLieComb c v w ↔ IsCombAtG t x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => hp.1.hom_ext ?_ ?_,
        inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (GlobalTheory.Frames.spMap_epsScaleR_comp (c i)).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEpsG x ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x ⟶ t.G) => (List.ofFn q).prod.left) this
  refine ⟨fun w hw => ⟨up w hw.1, hup _ _⟩, fun n v => ⟨fun hB => ⟨fun i => (tan _).1 (hB.1 i), fun w hw => ?_⟩,
    fun hB => ⟨fun i => (tan _).2 (hB.1 i), fun w hw => ?_⟩⟩⟩
  · have h := hB.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))
    simp only [comb, hup] at h
    exact h
  · have h := hB.2 _ ((tan _).1 hw)
    simp only [comb]
    exact h

theorem tanBasis_baseChange {X : Scheme.{0}} (t : SAB H X) {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    (x : Sp S ⟶ X) (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i))
    (hv' : ∀ w, IsTanAtG t x w → ∃! a : Fin n → S, IsCombAtG t x v a w) :
    (∀ i, IsTanAtG t (spMap φ ≫ x) (spMap (dualMap φ) ≫ v i)) ∧
      ∀ w, IsTanAtG t (spMap φ ≫ x) w →
        ∃! a : Fin n → T, IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) a w := by
  have := t.semi.comm
  have := t.semi.smooth
  have h₁ := isGrpPullback_pullback t.G x
  have h₂ := isGrpPullback_pullback ((Over.pullback x).obj t.G) (spMap φ)
  have h₃ := h₂.comp h₁
  have : IsCommMonObj ((Over.pullback x).obj t.G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj t.G)) :=
    Functor.isCommMonObj_obj
  obtain ⟨a₁, b₁⟩ := lieBasis_iff t x _ _ h₁
  obtain ⟨-, b₃⟩ := lieBasis_iff t _ _ _ h₃
  choose u hu using fun i => a₁ (v i) (hv i)
  have hb : IsLieBasis u := (b₁ n u).2 ⟨fun i => by rw [hu]; exact hv i, by rw [funext hu]; exact hv'⟩
  have hs : Smooth ((Over.pullback x).obj t.G).hom :=
    inferInstanceAs (Smooth (pullback.snd t.G.hom x))
  obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange S T φ _ _ _ h₂ hs n u hb
  have e : Chart.dualMapR φ = dualMap φ := by
    ext a <;> rfl
  have key := (b₃ n u').1 hb'
  have e' : ∀ i, (u' i).left ≫ pullback.fst ((Over.pullback x).obj t.G).hom (spMap φ) ≫ pullback.fst t.G.hom x =
      spMap (dualMap φ) ≫ v i := fun i => by
    rw [← Category.assoc, hu', e, Category.assoc, hu]
  refine ⟨fun i => e' i ▸ key.1 i, ?_⟩
  rw [← funext e']
  exact key.2

theorem spMap_dualMap_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    spMap (dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) := by
  rw [TanMod.spMap_comp', TanMod.spMap_comp']
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap, epsMul, mul_comm]

theorem frameBase : GlobalTheory.LocM.Cht.FrameBaseSt := by
  intro E _ _ _ H Dw l c X t R R' _ _ f x φ u h
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  have h1 := (eigBasis_iff c t f x u _ e (fun τ i => (h.1 τ i).1) (fun τ i => (h.1 τ i).2)).1 h.2
  obtain ⟨h2, h3⟩ := tanBasis_baseChange t φ x _ _ (fun j => (h.1 (e j).1 (e j).2).1) h1
  have ht : ∀ τ i, IsTanAtG t (spMap φ ≫ x) (u.bc φ τ i) := fun τ i => by
    have := h2 (e.symm ⟨τ, i⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this
  have he : ∀ τ i (a : 𝓞 E), u.bc φ τ i ≫ (t.act.act a).left =
      spMap (epsMul ((φ.comp f) (embK c τ a))) ≫ u.bc φ τ i := fun τ i a => by
    rw [Vecs.bc, Category.assoc, (h.1 τ i).2 a, ← Category.assoc, spMap_dualMap_epsMul, Category.assoc, RingHom.comp_apply]
  exact ⟨fun τ i => ⟨ht τ i, he τ i⟩, (eigBasis_iff c t (φ.comp f) _ (u.bc φ) _ e ht he).2 h3⟩

end GlobalTheory.LocM.FrameBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameMoveHolds
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.LocM.Cht

theorem isFrame_congr_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l l' : Level H} {c : Coeff l} {c' : Coeff l'} {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R]
    {f : c.F →+* R} {f' : c'.F →+* R} (h : ∀ τ a, f' (embK c' τ a) = f (embK c τ a)) (x : Sp R ⟶ X) (u : Vecs Dw t R) :
    GlobalTheory.LocM.IsFrame t f' x u ↔ GlobalTheory.LocM.IsFrame t f x u := by
  simp only [GlobalTheory.LocM.IsFrame, h]

theorem frameMove : FrameMoveSt := by
  intro E _ _ _ H Dw l l' c c' X X' t t' g m R _ f f' x h
  refine ⟨fun u' hu => ?_, fun u hu => ?_⟩
  · exact (BaseMdl.frame_push m f u' fun τ i => (hu.1 τ i).1.1).1 ((isFrame_congr_coeff t' h x u').1 hu)
  · choose u' h1 h2 using fun τ i => BaseMdl.exists_lift m (hu.1 τ i).1.1
    refine ⟨u', (isFrame_congr_coeff t' h x u').2 ((BaseMdl.frame_push m f u' h2).2 ?_), h1⟩
    rw [show (fun τ i => u' τ i ≫ m.φ : Vecs Dw t R) = u from funext fun τ => funext fun i => h1 τ i]
    exact hu

end GlobalTheory.LocM.Cht
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupLeBaseLatticeLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem reL_symm_reL_self {E : Type} [Field E] [NumberField E] {a b : ℕ} (h : a = b) (L : Submodule (𝓞 E) (Fin a → E)) :
    reL h.symm (reL h L) = L := by
  subst h
  rw [Formalism.L2.Forms.reL_rfl, Formalism.L2.Forms.reL_rfl]

set_option maxHeartbeats 4000000 in

theorem chart_Uloc_le_levelVL_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0 := by
  intro B X I hI hP l Z Ch0 chOf0 F u a Q h1 Ch _ chOf K g _ hStd _ hRd _ _ Lb0 hLb β v _
  obtain ⟨k, H, -⟩ := hRd
  obtain ⟨c0⟩ := GlobalTheory.Mem.Col2.TC.stepBefore_cl_nonempty I hI u
  obtain ⟨k', H'⟩ := (hStd u).mid (B.R.m - 1) h1 (succ_pred_m _)
  have hKb : (K β).lev.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 := by
    rw [← hLb]
    ext x
    rw [← (F u).levJ_Lb h1 (chOf0 u (B.R.m - 1) c0)]
    exact (H.lb β x).trans (H'.lb _ x).symm
  have hle := (GlobalTheory.Port.formsLev_re (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (I.rec7 l Z).sp.cm.sig
    ((I.rec7 l Z).sp.X (B.R.m - 1)).gram (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _))
    (fun _ _ => rfl) (K β).lev v).1
  rw [hKb, reL_symm_reL_self] at hle
  exact hle

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRootsHolds
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht

namespace GlobalTheory.LocM.RootsPrescribe

theorem exists_smul_of_mem_of_coprime {R L : Type*} [CommRing R] [AddCommGroup L] [Module R L] {I J : Ideal R} {r : R}
    (hc : I ⊔ J = ⊤) (hp : I * J = Ideal.span {r}) {x : L} (hI : x ∈ I • (⊤ : Submodule R L))
    (hJ : x ∈ J • (⊤ : Submodule R L)) : ∃ b, x = r • b := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (show (1 : R) ∈ I ⊔ J from hc ▸ Submodule.mem_top)
  have h1 : u • x ∈ (I * J) • (⊤ : Submodule R L) := by
    rw [mul_smul]; exact Submodule.smul_mem_smul hu hJ
  have h2 : v • x ∈ (I * J) • (⊤ : Submodule R L) := by
    rw [mul_comm, mul_smul]; exact Submodule.smul_mem_smul hv hI
  have h3 : x ∈ (I * J) • (⊤ : Submodule R L) := by
    have := Submodule.add_mem _ h1 h2
    rwa [← add_smul, huv, one_smul] at this
  rw [hp, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨b, -, hb⟩ := h3
  exact ⟨b, hb.symm⟩

theorem exists_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (l : Level H) {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso Dw k Q act e) (hpq : 1 ≤ Dw.p + Dw.q) {m : ℕ} (hm : 0 < m) {w : kˣ}
    (hw : IsPrimitiveRoot w (l.A * m)) (hA : w ^ m = I.ζ l.A) :
    ∃ I' : TateIso Dw k Q act e, I'.ζ (l.A * m) = w ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), I'.ev l.M a = I.ev l.M a := by
  have hN : 0 < l.A * m := Nat.mul_pos l.A_pos hm
  have hM : 0 < l.M := by have := l.three_le; omega
  have : NeZero (l.A * m) := ⟨hN.ne'⟩
  have hζ : IsPrimitiveRoot ((I.ζ (l.A * m) : kˣ) : k) (l.A * m) := IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim _ hN)
  obtain ⟨i, -, hi, hiz⟩ := (hζ.isPrimitiveRoot_iff).1 (IsPrimitiveRoot.coe_units_iff.2 hw)
  have hiz' : I.ζ (l.A * m) ^ i = w := Units.ext (by rw [Units.val_pow_eq_pow_val, hiz])
  have hi1 : (l.A : ℤ) ∣ (i : ℤ) - 1 := by
    rw [← (I.ζ_prim l.A l.A_pos).zpow_eq_one_iff_dvd, zpow_sub, zpow_one, zpow_natCast, mul_inv_eq_one]
    conv_lhs => rw [← I.ζ_pow l.A m l.A_pos hm, ← pow_mul, mul_comm m, pow_mul, hiz', hA]
  obtain ⟨g, hg, -, hgM, hgA⟩ := GlobalTheory.SimMult.exists_sim_trivial_of_mult GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift E H Dw
    l (l.A * m) i hN (Nat.isCoprime_iff_coprime.2 hi) hi1
  refine ⟨GlobalTheory.LevelTwist.twist I g ((GlobalTheory.SimAlg.sim_group E H Dw hpq).1 g), ?_, fun a => ?_, fun a ha => ?_⟩
  · rw [GlobalTheory.LevelTwist.twist_ζ, GlobalTheory.LevelTwist.zeta_zpow_congr I hN hg, zpow_natCast, hiz']
  · exact GlobalTheory.LevelTwist.ev_congr I l.A_pos (hgA a)
  · refine GlobalTheory.LevelTwist.ev_congr I hM ?_
    obtain ⟨b, hb⟩ := exists_smul_of_mem_of_coprime l.coprime l.prod (hgM a)
      (Submodule.sub_mem _ (GlobalTheory.LevelTwist.map_mem_smul_top _ _ ha) ha)
    exact ⟨b, hb.trans (Nat.cast_smul_eq_nsmul _ _ _)⟩

theorem roots : GlobalTheory.LocM.Cht.RootsSt := by
  intro E _ _ _ H Dw l k _ Q _ act e I z hpq hz hzp hA
  have hM : 0 < l.M := by have := l.three_le; omega
  have key := fun j : ℕ => exists_one l I hpq j.factorial_pos (hz _ (Nat.mul_pos l.A_pos j.factorial_pos))
    ((hzp _ _ l.A_pos j.factorial_pos).trans hA)
  choose J hJ hJA hJM using key
  obtain ⟨I', hI'⟩ := GlobalTheory.Ex.TateLimit.exists_limit E H Dw k Q act e J
  refine ⟨I', fun n hn => ?_, fun a => ?_, fun a ha => ?_⟩
  · obtain ⟨j, hj, -, h⟩ := hI' n hn n
    obtain ⟨t, ht⟩ : n ∣ l.A * j.factorial := (Nat.dvd_factorial hn hj).mul_left _
    have ht0 : 0 < t := Nat.pos_of_mul_pos_left (ht ▸ Nat.mul_pos l.A_pos j.factorial_pos : 0 < n * t)
    rw [h, ← (J j).ζ_pow n t hn ht0, ← hzp n t hn ht0, ← ht, hJ]
  · obtain ⟨j, -, h, -⟩ := hI' l.A l.A_pos 0
    rw [h, hJA]
  · obtain ⟨j, -, h, -⟩ := hI' l.M hM 0
    rw [h, hJM j a ha]

end GlobalTheory.LocM.RootsPrescribe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateHermitianSmooth
section
open AlgebraicGeometry CategoryTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.GradedNorm
open scoped ComplexOrder

namespace GlobalTheory

open scoped ContDiff

theorem AnRead.smoothOn_conjTranspose_mul_mul :
    ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D m : ℕ} (R : AnRead p σ D) (S : Set (CxPts p σ)), IsOpen S → ∀ (A M : CxPts p σ → Matrix (Fin m) (Fin m) ℂ), (∀ a b, R.HoloOn S (fun y => A y a b)) → (∀ a b, R.SmoothOn S (fun y => (M y a b).re) ∧ R.SmoothOn S (fun y => (M y a b).im)) → ∀ a b : Fin m, R.SmoothOn S (fun y => (((A y)ᴴ * M y * A y) a b).re) ∧ R.SmoothOn S (fun y => (((A y)ᴴ * M y * A y) a b).im) := by
  intro k _ Y p σ D m R S hS A M hA hM a b
  have hC : ∀ i, ContDiffOn ℝ ∞ ((fun y => ((A y)ᴴ * M y * A y) a b) ∘ (R.chart i).e.symm)
      ((R.chart i).e.target ∩ (R.chart i).e.symm ⁻¹' S) := by
    intro i
    set e := (R.chart i).e
    have hU := GlobalTheory.ChartGlue.isOpen_over e hS
    have hAe : ∀ c d, ContDiffOn ℝ ∞ (fun v => A (e.symm v) c d) (e.target ∩ e.symm ⁻¹' S) :=
      fun c d => GlobalTheory.ChartGlue.contDiffOn_real hU (hA c d i)
    have hAc : ∀ c d, ContDiffOn ℝ ∞ (fun v => star (A (e.symm v) c d)) (e.target ∩ e.symm ⁻¹' S) :=
      fun c d => Complex.conjCLE.contDiff.comp_contDiffOn (hAe c d)
    have hMe : ∀ c d, ContDiffOn ℝ ∞ (fun v => M (e.symm v) c d) (e.target ∩ e.symm ⁻¹' S) := by
      intro c d
      have h1 : ContDiffOn ℝ ∞ (fun v => (M (e.symm v) c d).re) (e.target ∩ e.symm ⁻¹' S) := (hM c d).1 i
      have h2 : ContDiffOn ℝ ∞ (fun v => (M (e.symm v) c d).im) (e.target ∩ e.symm ⁻¹' S) := (hM c d).2 i
      have hf : (fun v => M (e.symm v) c d) = fun v => (((M (e.symm v) c d).re : ℝ) : ℂ) +
          (((M (e.symm v) c d).im : ℝ) : ℂ) * Complex.I := by
        funext v; exact (Complex.re_add_im _).symm
      rw [hf]
      exact (Complex.ofRealCLM.contDiff.comp_contDiffOn h1).add
        ((Complex.ofRealCLM.contDiff.comp_contDiffOn h2).mul contDiffOn_const)
    show ContDiffOn ℝ ∞ (fun v => ((A (e.symm v))ᴴ * M (e.symm v) * A (e.symm v)) a b) _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact ContDiffOn.sum fun x _ => (ContDiffOn.sum fun c _ => (hAc c a).mul (hMe c x)).mul (hAe x b)
  exact ⟨fun i => Complex.reCLM.contDiff.comp_contDiffOn (hC i),
    fun i => Complex.imCLM.contDiff.comp_contDiffOn (hC i)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnKeySectionComplexValueStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_keySection_complexValue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (T : ∀ k, ThetaData e F M k) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → (∀ k, IsNormUn (T k) (un k)) → FramesOK e F M un → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (ρ : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → (∀ b ∈ B, RootVal (unfOf e F M un) (y b) (ρ b)) → ContinuousOn ρ B := by
  first | exact @GlobalTheory.KeyFourth.continuousOn_rootVal | exact GlobalTheory.KeyFourth.continuousOn_rootVal | (intros; apply GlobalTheory.KeyFourth.continuousOn_rootVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CorrespondenceDiagonalStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.correspondence_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), N2 Y → ∀ Z₁ Z₂ : Mdl Y i₀, GlobalTheory.LocM.Corr Z₁ Z₂ → IsDiag Z₁ Z₂ (diagCl Z₁ Z₂) := by
  first | exact @GlobalTheory.LocM.Diag.isDiag_diagCl | exact GlobalTheory.LocM.Diag.isDiag_diagCl | (intros; apply GlobalTheory.LocM.Diag.isDiag_diagCl <;> assumption)
end

