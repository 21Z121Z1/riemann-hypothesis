import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierTrivialization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2551
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackOfIsOpenImmersion
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res
  pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)

namespace GlobalTheory.FlagLocal

variable {X Y S : Scheme.{0}} {A A' A'' E E' : X.Modules}

def Same (u : A ⟶ E) (v : A' ⟶ E) : Prop := ∃ e : A ≅ A', e.hom ≫ v = u

theorem Same.refl (u : A ⟶ E) : Same u u := ⟨Iso.refl _, Category.id_comp _⟩

theorem Same.symm {u : A ⟶ E} {v : A' ⟶ E} (h : Same u v) : Same v u :=
  have ⟨e, he⟩ := h
  ⟨e.symm, by rw [← he]; simp⟩

theorem Same.trans {u : A ⟶ E} {v : A' ⟶ E} {w : A'' ⟶ E} (h : Same u v) (h' : Same v w) : Same u w :=
  have ⟨e, he⟩ := h
  have ⟨e', he'⟩ := h'
  ⟨e ≪≫ e', by rw [← he, ← he']; simp⟩

theorem Same.comp {u : A ⟶ E} {v : A' ⟶ E} (h : Same u v) (φ : E ⟶ E') : Same (u ≫ φ) (v ≫ φ) :=
  have ⟨e, he⟩ := h
  ⟨e, by rw [← he, Category.assoc]⟩

theorem same_comp_iff {u : A ⟶ E} {v : A' ⟶ E} (φ : E ⟶ E') [Mono φ] : Same (u ≫ φ) (v ≫ φ) ↔ Same u v :=
  ⟨fun ⟨e, he⟩ => ⟨e, by rw [← cancel_mono φ, Category.assoc, he]⟩, fun h => h.comp φ⟩

theorem Same.pull {u : A ⟶ E} {v : A' ⟶ E} (h : Same u v) (f : Y ⟶ X) :
    Same ((Scheme.Modules.pullback f).map u) ((Scheme.Modules.pullback f).map v) :=
  have ⟨e, he⟩ := h
  ⟨(Scheme.Modules.pullback f).mapIso e, by rw [← he]; simp⟩

theorem same_of_le_le {u : A ⟶ E} {v : A' ⟶ E} [Mono u] [Mono v] (f : A ⟶ A') (g : A' ⟶ A)
    (hf : f ≫ v = u) (hg : g ≫ u = v) : Same u v :=
  ⟨⟨f, g, by rw [← cancel_mono u, Category.assoc, hg, hf, Category.id_comp],
    by rw [← cancel_mono v, Category.assoc, hf, hg, Category.id_comp]⟩, hf⟩

theorem cokernel_app_eq_zero_iff (v : A ⟶ E) [Mono v] (V : X.Opens) (t : Γ(E, V)) :
    (cokernel.π v).app V t = 0 ↔ ∃ m, v.app V m = t :=
  QCoh.exact_app_of_exact_of_mono (ShortComplex.exact_cokernel v) V t

theorem exists_fac_of_sections (u : A ⟶ E) (v : A' ⟶ E) [Mono v]
    (h : ∀ (V : X.Opens) (s : Γ(A, V)), ∃ m, v.app V m = u.app V s) : ∃ f : A ⟶ A', f ≫ v = u := by
  have : u ≫ cokernel.π v = 0 := by
    refine Scheme.Modules.hom_ext _ _ fun V => ?_
    ext s
    exact (cokernel_app_eq_zero_iff v V _).2 (h V s)
  exact ⟨Abelian.monoLift v u this, Abelian.monoLift_comp _ _ _⟩

theorem same_of_range {u : A ⟶ E} {v : A' ⟶ E} [Mono u] [Mono v]
    (h : ∀ V : X.Opens, Set.range (u.app V) = Set.range (v.app V)) : Same u v := by
  obtain ⟨f, hf⟩ := exists_fac_of_sections u v fun V s => (h V).le ⟨s, rfl⟩
  obtain ⟨g, hg⟩ := exists_fac_of_sections v u fun V s => (h V).ge ⟨s, rfl⟩
  exact same_of_le_le f g hf hg

theorem bijective_pullbackSections (a : Y ⟶ X) [IsOpenImmersion a] (E : X.Modules) {V : X.Opens}
    (hV : V ≤ a.opensRange) {W : Y.Opens} (hW : W = a ⁻¹ᵁ V) :
    Function.Bijective (pullbackSections a E hW.le) := by
  subst hW
  have e := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction a)
    (Scheme.Modules.pullbackPushforwardAdjunction a) E
  have h1 : Function.Bijective (E.presheaf.map (homOfLE (a.image_preimage_le V)).op) :=
    QCoh.res_bijective_of_eq E _ (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_eq_right.2 hV)
  have h2 := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctorIsoPullback a).hom.app E).app (a ⁻¹ᵁ V))
  convert h2.comp h1 using 1
  funext s
  exact (resM_self _ _).trans congr(($e).app V s).symm

theorem mem_range_of_pullback (a : Y ⟶ X) [IsOpenImmersion a] (v : A ⟶ E) {V : X.Opens}
    (hV : V ≤ a.opensRange) {W : Y.Opens} (hW : W = a ⁻¹ᵁ V) (t : Γ(E, V))
    (h : ∃ m, ((Scheme.Modules.pullback a).map v).app W m = pullbackSections a E hW.le t) :
    ∃ m, v.app V m = t := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨m, rfl⟩ := (bijective_pullbackSections a A hV hW).2 m
  rw [pullback_map_app_pullbackSections] at hm
  exact ⟨m, (bijective_pullbackSections a E hV hW).1 hm⟩

theorem mono_pullback_of_isOpenImmersion (a : Y ⟶ X) [IsOpenImmersion a] (v : A ⟶ E) [Mono v] :
    Mono ((Scheme.Modules.pullback a).map v) := by
  refine QCoh.mono_of_locally_app_injective _ fun W _ hx => ⟨W, hx, le_rfl, fun s t h => ?_⟩
  have hW := (a.preimage_image_eq W).symm
  have hV := a.image_le_opensRange W
  obtain ⟨s, rfl⟩ := (bijective_pullbackSections a A hV hW).2 s
  obtain ⟨t, rfl⟩ := (bijective_pullbackSections a A hV hW).2 t
  rw [pullback_map_app_pullbackSections, pullback_map_app_pullbackSections] at h
  rw [QCoh.injective_app_of_mono v _ ((bijective_pullbackSections a E hV hW).1 h)]

section Cover

variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]

theorem exists_fac_of_cover (hc : ∀ x : X, ∃ i y, a i y = x) (u : A ⟶ E) (v : A' ⟶ E) [Mono v]
    (h : ∀ i, ∃ f, f ≫ (Scheme.Modules.pullback (a i)).map v = (Scheme.Modules.pullback (a i)).map u) :
    ∃ f : A ⟶ A', f ≫ v = u := by
  refine exists_fac_of_sections u v fun V s => (cokernel_app_eq_zero_iff v V _).1 ?_
  refine (Sub.ker (cokernel.π v)).mem_of_local (V := V) (s := u.app V s) fun x hx => ?_
  obtain ⟨i, y, rfl⟩ := hc x
  obtain ⟨f, hf⟩ := h i
  refine ⟨V ⊓ (a i).opensRange, inf_le_left, ⟨hx, y, rfl⟩, (cokernel_app_eq_zero_iff v _ _).2 ?_⟩
  refine mem_range_of_pullback (a i) v inf_le_right rfl _
    ⟨f.app _ (pullbackSections (a i) A le_rfl (resM A inf_le_left s)), ?_⟩
  rw [QCoh.app_app, hf, pullback_map_app_pullbackSections, app_resM]

theorem same_of_cover (hc : ∀ x : X, ∃ i y, a i y = x) {u : A ⟶ E} {v : A' ⟶ E} [Mono u] [Mono v]
    (h : ∀ i, Same ((Scheme.Modules.pullback (a i)).map u) ((Scheme.Modules.pullback (a i)).map v)) :
    Same u v := by
  obtain ⟨f, hf⟩ := exists_fac_of_cover a hc u v fun i => have ⟨e, he⟩ := h i; ⟨e.hom, he⟩
  obtain ⟨g, hg⟩ := exists_fac_of_cover a hc v u fun i => have ⟨e, he⟩ := (h i).symm; ⟨e.hom, he⟩
  exact same_of_le_le f g hf hg

theorem isVB_of_openImmersions (hc : ∀ x : X, ∃ i y, a i y = x) {r : ℕ}
    (h : ∀ i, IsVB ((Scheme.Modules.pullback (a i)).obj A) r) : IsVB A r := fun x => by
  obtain ⟨i, y, rfl⟩ := hc x
  obtain ⟨W, e, hy, he⟩ :=
    (h i).of_iso ((Scheme.Modules.restrictFunctorIsoPullback (a i)).app A).symm y
  exact ⟨a i ''ᵁ W, e, ⟨y, hy, rfl⟩, (isFrame_restrict_iff (a i) e).1 he⟩

variable {G : ∀ i, (T i).Modules} (v : ∀ i, G i ⟶ (Scheme.Modules.pullback (a i)).obj E)

def glueSub : Sub E :=
  Sub.iInf fun i => Sub.ker ((Scheme.Modules.pullbackPushforwardAdjunction (a i)).unit.app E ≫
    (Scheme.Modules.pushforward (a i)).map (cokernel.π (v i)))

omit [∀ i, IsOpenImmersion (a i)] in
theorem mem_glueSub_iff [∀ i, Mono (v i)] {V : X.Opens} {s : Γ(E, V)} :
    s ∈ (glueSub a v).sec V ↔ ∀ i, ∃ m, (v i).app _ m = pullbackSections (a i) E le_rfl s := by
  refine (Submodule.mem_iInf _).trans (forall_congr' fun i => ?_)
  rw [← cokernel_app_eq_zero_iff]
  have : pullbackSections (a i) E le_rfl s =
      ((Scheme.Modules.pullbackPushforwardAdjunction (a i)).unit.app E).app V s := resM_self _ _
  rw [this]
  exact Iff.rfl

def Compat : Prop := ∀ i j (S : Scheme.{0}) (b : S ⟶ T i) (c : S ⟶ T j) (w : b ≫ a i = c ≫ a j),
  Same ((Scheme.Modules.pullback b).map (v i) ≫ (Scheme.Modules.pullbackComp b (a i)).hom.app E ≫
      (Scheme.Modules.pullbackCongr w).hom.app E)
    ((Scheme.Modules.pullback c).map (v j) ≫ (Scheme.Modules.pullbackComp c (a j)).hom.app E)

theorem mem_glueSub_of_le [∀ i, Mono (v i)] (hv : Compat a v) (i : J) {V : X.Opens}
    (hV : V ≤ (a i).opensRange) {s : Γ(E, V)} {W : (T i).Opens} (hW : W = a i ⁻¹ᵁ V)
    (hs : ∃ m, (v i).app W m = pullbackSections (a i) E hW.le s) : s ∈ (glueSub a v).sec V := by
  subst hW
  obtain ⟨m, hm⟩ := hs
  refine (mem_glueSub_iff a v).2 fun j => ?_
  let b := pullback.fst (a i) (a j)
  let c := pullback.snd (a i) (a j)
  have w : b ≫ a i = c ≫ a j := pullback.condition
  obtain ⟨e, he⟩ := hv i j _ b c w
  have hr : a j ⁻¹ᵁ V ≤ c.opensRange := by
    intro y hy
    obtain ⟨z, hz⟩ := hV hy
    obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback z y hz
    exact ⟨p, hp⟩
  have hle : c ⁻¹ᵁ a j ⁻¹ᵁ V ≤ b ⁻¹ᵁ a i ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
  have key : e.hom ≫ (Scheme.Modules.pullback c).map (v j) = (Scheme.Modules.pullback b).map (v i) ≫
      (Scheme.Modules.pullbackComp b (a i) ≪≫ Scheme.Modules.pullbackCongr w ≪≫
        (Scheme.Modules.pullbackComp c (a j)).symm).hom.app E := by
    rw [← cancel_mono ((Scheme.Modules.pullbackComp c (a j)).hom.app E), Category.assoc, he]
    simp
  refine mem_range_of_pullback c (v j) hr rfl _ ⟨e.hom.app _ (pullbackSections b _ hle m), ?_⟩
  rw [← Vert.DivPull.pullbackSquare_app w E le_rfl hle le_rfl le_rfl, ← hm,
    ← pullback_map_app_pullbackSections, QCoh.app_app, key]
  first | exact (QCoh.app_app _ _ _ _).symm | rfl

theorem same_glueSub [∀ i, Mono (v i)] (hv : Compat a v) (i : J) :
    Same ((Scheme.Modules.pullback (a i)).map (glueSub a v).incl) (v i) := by
  have := mono_pullback_of_isOpenImmersion (a i) (glueSub a v).incl
  refine same_of_range fun W => ?_
  have hW := ((a i).preimage_image_eq W).symm
  have hV := (a i).image_le_opensRange W
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨s, rfl⟩ := (bijective_pullbackSections (a i) _ hV hW).2 s
    obtain ⟨m, hm⟩ := (mem_glueSub_iff a v).1 ((glueSub a v).incl_app_mem s) i
    refine ⟨resM _ hW.le m, ?_⟩
    rw [app_resM, hm, pullback_map_app_pullbackSections]
    exact res_pullbackSections _ _ _ _ _
  · rintro ⟨m, rfl⟩
    obtain ⟨s, hs⟩ := (bijective_pullbackSections (a i) _ hV hW).2 ((v i).app W m)
    refine ⟨pullbackSections (a i) _ hW.le ((glueSub a v).mkSec s
      (mem_glueSub_of_le a v hv i hV hW ⟨m, hs.symm⟩)), ?_⟩
    rw [pullback_map_app_pullbackSections, Sub.incl_app_mkSec, hs]

theorem exists_flag_of_cover (hc : ∀ x : X, ∃ i y, a i y = x) {n : ℕ}
    (fl : ∀ i, Vert.Flag ((Scheme.Modules.pullback (a i)).obj E) n)
    (h : ∀ k, Compat a fun i => (fl i).ι k) :
    ∃ fl₀ : Vert.Flag E n, ∀ i k, Same ((Scheme.Modules.pullback (a i)).map (fl₀.ι k)) ((fl i).ι k) := by
  let N : Fin (n + 1) → Sub E := fun k => glueSub a fun i => (fl i).ι k
  have hN := fun k i => same_glueSub a (fun i => (fl i).ι k) (h k) i
  have hstep : ∀ (k : Fin n) V s, (N k.castSucc).incl.app V s ∈ (N k.succ).sec V := fun k V s =>
    (mem_glueSub_iff a _).2 fun i => by
      obtain ⟨m, hm⟩ := (mem_glueSub_iff a _).1 ((N k.castSucc).incl_app_mem s) i
      exact ⟨((fl i).step k).app _ m, by rw [QCoh.app_app, (fl i).step_ι, hm]⟩
  refine ⟨{ F := fun k => (N k).toMod
            ι := fun k => (N k).incl
            isSubbundle := fun k => ⟨inferInstance, n - k, isVB_of_openImmersions a hc fun i => ?_⟩
            isVB := fun k => isVB_of_openImmersions a hc fun i => ?_
            step := fun k => (N k.succ).lift _ (hstep k)
            step_ι := fun k => (N k.succ).lift_incl _ (hstep k)
            isIso_last := ?_ }, fun i k => hN k i⟩
  · obtain ⟨e, he⟩ := hN k i
    exact ((fl i).isVB_cokernel k).of_iso ((cokernelEpiComp e.hom _).symm ≪≫ cokernelIsoOfEq he ≪≫
      (PreservesCokernel.iso (Scheme.Modules.pullback (a i)) (N k).incl).symm)
  · obtain ⟨e, -⟩ := hN k i
    exact ((fl i).isVB k).of_iso e.symm
  · refine Twist.isIso_of_bijective _ fun V => ⟨(N _).incl_app_injective V, fun s => ?_⟩
    exact (N _).mem_sec_iff.1 ((mem_glueSub_iff a _).2 fun i =>
      (ConcreteCategory.bijective_of_isIso (((fl i).ι (Fin.last n)).app _)).2 _)

end Cover

end GlobalTheory.FlagLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismEqOfEqOnThickenings
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem hom_eq_of_reductions_eq : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  intro R _ _ I hI X Z hX hZ Y b hb g g' hg
  have hι : IsClosedImmersion (equalizer.ι g g').left := isClosedImmersion_equalizer_ι_left g g'
  have hN : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hle : ∀ e : ℕ, (equalizer.ι g g').left.ker ≤ baseIdeal X.hom (I ^ (e + 1)) := by
    intro e
    rw [← (GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) X.left (Y e).left X.hom (b e) (Y e).hom (hb e)).2.1]
    let c : Over.mk (b e ≫ X.hom) ⟶ X := Over.homMk (b e) rfl
    have hc : c ≫ g = c ≫ g' := by
      ext
      exact hg e
    have h1 : (equalizer.lift c hc).left ≫ (equalizer.ι g g').left = b e := by
      rw [← Over.comp_left, equalizer.lift_ι]
      rfl
    rw [← h1]
    exact Scheme.Hom.le_ker_comp _ _
  have hbot : (equalizer.ι g g').left.ker ≤ ⊥ :=
    GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson R I hI X.left X.hom _ ⊥ inferInstance fun e => (hle e).trans le_sup_right
  have hiso : IsIso (equalizer.ι g g').left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.2 (le_bot_iff.1 hbot)
  ext
  rw [← cancel_epi (equalizer.ι g g').left, ← Over.comp_left, ← Over.comp_left, equalizer.condition]

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackTrivialOfImFormInt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

namespace GlobalTheory.TorusRM.KerTriv

open GlobalTheory.TorusRM.TransFrame

theorem dot_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (a b : Fin g → ℂ) :
    a ⬝ᵥ Hm *ᵥ star b = star (b ⬝ᵥ Hm *ᵥ star a) := by
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply i j, star_star]
  ring

theorem exp_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (w l : Fin g → ℂ) (n : ℤ)
    (hn : (w ⬝ᵥ Hm *ᵥ star l).im = n) :
    Complex.exp (Real.pi * (l ⬝ᵥ Hm *ᵥ star w)) = Complex.exp (Real.pi * (w ⬝ᵥ Hm *ᵥ star l)) := by
  rw [dot_herm_swap hH l w]
  set a := w ⬝ᵥ Hm *ᵥ star l
  have e : (star a : ℂ) = a + (-n : ℤ) * (2 * Complex.I) := by
    apply Complex.ext <;> simp [hn, Complex.conj_re, Complex.conj_im] <;> ring
  rw [e, mul_add, Complex.exp_add]
  have : (Real.pi : ℂ) * ((-n : ℤ) * (2 * Complex.I)) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, _root_.mul_one]

end GlobalTheory.TorusRM.KerTriv

open GlobalTheory.TorusRM.TransFrame GlobalTheory.TorusRM.KerTriv in

theorem GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ w : Fin g → ℂ, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → ∃ t : ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left).Gen, t.IsGen := by
  intro A _ _ g hA M u Hm χ hM hF w hw
  have hp : IsProjOver A.hom :=
    (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1 (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hL' : ((abelian₂ A M).pull (pairRight (u.ex w)).left).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨t, ht⟩ := GlobalTheory.HolUnifSec.hasGen_of_periodic A hA hp _ hL' g (transUnif u w)
    (fun z => Complex.exp (Real.pi * (z ⬝ᵥ Hm *ᵥ star w))) (by
      have hd : Differentiable ℂ (fun z : Fin g → ℂ => z ⬝ᵥ Hm *ᵥ star w) := by
        simp only [dotProduct]; fun_prop
      exact ((differentiable_const _).mul hd).cexp) (fun z => Complex.exp_ne_zero _) (by
      intro l hl i z hz
      obtain ⟨n, hn⟩ := hw l hl
      rw [transUnif_factor u hF w ⟨l, hl⟩ i z hz, add_dotProduct, mul_add, Complex.exp_add,
        exp_swap hF.1 w l n hn]
      ring)
  have hρ : fst A (𝟙_ (Over (Sp ℂ))) ≫ pairRight (u.ex w) =
      lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w) := by
    simp only [pairRight, comp_lift, Category.comp_id]
    rw [← Category.assoc, toUnit_unique (fst A (𝟙_ (Over (Sp ℂ))) ≫ toUnit A) (snd A (𝟙_ (Over (Sp ℂ))))]
  have key : (fun _ : PUnit => (fst A (𝟙_ (Over (Sp ℂ)))).left ≫ (pairRight (u.ex w)).left) =
      (fun _ : PUnit => (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left) := by
    funext _
    rw [← Over.comp_left, hρ]
  have H : ∃ t : (LB.LinComb (abelian₂ A M) (fun _ : PUnit => (fst A (𝟙_ (Over (Sp ℂ)))).left ≫
      (pairRight (u.ex w)).left) (fun _ => 1)).Gen, t.IsGen :=
    ⟨_, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen (abelian₂ A M) _ _ t ht (fst A (𝟙_ (Over (Sp ℂ)))).left⟩
  rw [key] at H
  exact H
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootExistsOverFgSubalgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

noncomputable section

open GlobalTheory

namespace GlobalTheory.RootFG

theorem lbIso_of_factor {Y Y' X₀ : Scheme.{0}} {M N : LB X₀} (a : Y ⟶ X₀) (j : Y' ⟶ Y) (a' : Y' ⟶ X₀)
    (e : a' = j ≫ a) (h : LBIso (M.pull a) (N.pull a)) : LBIso (M.pull a') (N.pull a') :=
  LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h

theorem exists_fg_lbIso_of_isPullback {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C] {X : Scheme.{0}}
    (pB : X ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB] {R₀ : Subalgebra k C} (h₀ : R₀.FG) {Y₀ Y : Scheme.{0}}
    (q₀ : Y₀ ⟶ Sp R₀) (a₀ : Y₀ ⟶ X) (hY₀ : IsPullback a₀ q₀ pB (spMap (algebraMap k R₀)))
    (y : Y ⟶ Y₀) (q : Y ⟶ Sp C) (hY : IsPullback y q q₀ (spMap R₀.val.toRingHom))
    (M N : LB Y₀) (hM : M.IsLB) (hN : N.IsLB) (H : LBIso (M.pull y) (N.pull y)) :
    ∃ (R : Subalgebra k C) (hR : R₀ ≤ R), R.FG ∧ ∀ (Y₁ : Scheme.{0}) (q₁ : Y₁ ⟶ Sp R) (y₁ : Y₁ ⟶ Y₀),
      y₁ ≫ q₀ = q₁ ≫ spMap (Subalgebra.inclusion hR).toRingHom → LBIso (M.pull y₁) (N.pull y₁) := by
  let e : pullback pB (spMap (algebraMap k R₀)) ⟶ Y₀ :=
    hY₀.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  have e₁ : e ≫ a₀ = pullback.fst _ _ := hY₀.lift_fst _ _ _
  have e₂ : e ≫ q₀ = pullback.snd _ _ := hY₀.lift_snd _ _ _
  let f : pullback pB (spMap (algebraMap k C)) ⟶ Y :=
    hY.lift (baseChangeMap pB R₀.val ≫ e) (pullback.snd _ _) (by
      rw [Category.assoc, e₂, baseChangeMap_snd])
  have hf : f ≫ y = baseChangeMap pB R₀.val ≫ e := hY.lift_fst _ _ _
  have H₀ : LBIso ((M.pull e).pull (baseChangeMap pB R₀.val)) ((N.pull e).pull (baseChangeMap pB R₀.val)) := by
    have := lbIso_of_factor y f _ hf.symm H
    exact LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _)
      (Spread.lbIso_pull_pull hM _ rfl).symm
      (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) this
        (Spread.lbIso_pull_pull hN _ rfl))
  obtain ⟨R, hR, hRfg, H₁⟩ := exists_fg_lbIso pB h₀ (M.pull e) (N.pull e) (pull_isLB hM _) (pull_isLB hN _) H₀
  refine ⟨R, hR, hRfg, fun Y₁ q₁ y₁ w => ?_⟩
  have H₂ : LBIso (M.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e))
      (N.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e)) :=
    LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _)
      (Spread.lbIso_pull_pull hM _ rfl)
      (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) H₁
        (Spread.lbIso_pull_pull hN _ rfl).symm)
  have hs : spMap (Subalgebra.inclusion hR).toRingHom ≫ spMap (algebraMap k R₀) = spMap (algebraMap k R) := by
    rw [spMap_comp_ring]; rfl
  let m : Y₁ ⟶ pullback pB (spMap (algebraMap k R)) :=
    pullback.lift (y₁ ≫ a₀) q₁ (by rw [Category.assoc, hY₀.w, ← Category.assoc, w, Category.assoc, hs])
  refine lbIso_of_factor _ m y₁ ?_ H₂
  apply hY₀.hom_ext
  · rw [Category.assoc, Category.assoc, e₁, baseChangeMap_fst, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, e₂, baseChangeMap_snd, pullback.lift_snd_assoc, w]

end GlobalTheory.RootFG

open GlobalTheory GlobalTheory.RootFG in

theorem GlobalTheory.RootFG.root_fg : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left),
    P.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (C : Type) [CommRing C] [Algebra k C],
    Root A P (spMap (algebraMap k C) ≫ t) → ∃ B : Subalgebra k C, B.FG ∧ Root A P (spMap (algebraMap k B) ≫ t) := by
  intro S A _ hA P hP k _ t C _ _ hRt
  obtain ⟨B', _, _, β, β₂, hβ, hsq, L, hL, H⟩ := hRt
  obtain ⟨A₀, _, φ₀, h₀⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A t
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₀
  have := hA₀.proper
  have : IsProper (A₀ ⊗ A₀).hom := by
    change IsProper (pullback.fst A₀.hom A₀.hom ≫ A₀.hom)
    infer_instance

  let φ' : B'.left ⟶ A₀.left := h₀.1.lift β (B'.hom ≫ spMap (algebraMap k C)) (by rw [hβ.1.w, Category.assoc])
  have hφ'₁ : φ' ≫ φ₀ = β := h₀.1.lift_fst _ _ _
  have hφ'₂ : φ' ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k C) := h₀.1.lift_snd _ _ _
  have hB'₀ : IsGrpPullback B' A₀ (spMap (algebraMap k C)) φ' :=
    IsGrpPullback.cancel h₀ (by rw [hφ'₁]; exact hβ) hφ'₂

  obtain ⟨R₁, M, ρ, hR₁, hM, hρ₁, hρ₂, HL⟩ := GlobalTheory.LBDescent.exists_fg_lb A₀.hom B'.hom φ' hB'₀.1 L hL
  obtain ⟨B₁, _, β₁, h₁⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A₀ (spMap (algebraMap k R₁))
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ h₁
  haveI : IsCommMonObj B₁ := hB₁.comm
  let e₁ : B₁.left ⟶ pullback A₀.hom (spMap (algebraMap k R₁)) := h₁.1.isoPullback.hom
  let L₁ : LB B₁.left := M.pull e₁
  have hL₁ : L₁.IsLB := pull_isLB hM _
  let σ : Sp C ⟶ Sp R₁ := spMap R₁.val.toRingHom
  have hσ : σ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k C) := by
    rw [spMap_comp_ring]; rfl
  let ψ : B'.left ⟶ B₁.left := h₁.1.lift φ' (B'.hom ≫ σ) (by rw [hφ'₂, Category.assoc, hσ])
  have hψ₁ : ψ ≫ β₁ = φ' := h₁.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ B₁.hom = B'.hom ≫ σ := h₁.1.lift_snd _ _ _
  have hψ : IsGrpPullback B' B₁ σ ψ := IsGrpPullback.cancel h₁ (by rw [hψ₁, hσ]; exact hB'₀) hψ₂
  have hρψ : ρ = ψ ≫ e₁ := by
    apply pullback.hom_ext
    · rw [hρ₁, Category.assoc, IsPullback.isoPullback_hom_fst, hψ₁]
    · rw [hρ₂, Category.assoc, IsPullback.isoPullback_hom_snd, hψ₂]
  have HL₁ : LBIso L (L₁.pull ψ) :=
    LBIso.trans hL (pull_isLB hM _) (pull_isLB hL₁ _) HL (Spread.lbIso_pull_pull hM ψ hρψ)

  have hc : IsGrpPullback B₁ A (spMap (algebraMap k R₁) ≫ t) (β₁ ≫ φ₀) := h₁.comp h₀
  let β₂₁ := (lift (pushPt hc.1.w (fst B₁ B₁)) (pushPt hc.1.w (snd B₁ B₁))).left
  have hsq₁ : IsSquare (β₁ ≫ φ₀) β₂₁ := GlobalTheory.LamPull.exists_isSquare hc.1.w
  let V := lift (pushPt hψ.1.w (fst B' B')) (pushPt hψ.1.w (snd B' B'))
  have hsqψ : IsSquare ψ V.left := GlobalTheory.LamPull.exists_isSquare hψ.1.w
  have c₁ : LBIso (abelian₂ B' L) ((abelian₂ B₁ L₁).pull V.left) :=
    GlobalTheory.SymSpread.lbIso_cube hψ hL₁ hL HL₁ (x2 B₁) (x2 B') V (fun i => by fin_cases i <;> simp [V, x2])
  have hβ₂ : β₂ = V.left ≫ β₂₁ := by
    have h' := GlobalTheory.ZM.SiegPull.isSquare_comp hsqψ hsq₁
    have eβ : ψ ≫ β₁ ≫ φ₀ = β := by rw [← Category.assoc, hψ₁, hφ'₁]
    rw [eβ] at h'
    apply pullback.hom_ext
    · exact hsq.1.trans h'.1.symm
    · exact hsq.2.trans h'.2.symm
  have hΛ₁ : (abelian₂ B₁ L₁).IsLB := LB.isLB_linComb hL₁ _ _
  have hΛ' : (abelian₂ B' L).IsLB := LB.isLB_linComb hL _ _
  have HV : LBIso ((abelian₂ B₁ L₁).pull V.left) ((P.pull β₂₁).pull V.left) :=
    LBIso.trans (pull_isLB hΛ₁ _) hΛ' (pull_isLB (pull_isLB hP _) _) c₁.symm
      (LBIso.trans hΛ' (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) H (Spread.lbIso_pull_pull hP V.left hβ₂))

  obtain ⟨R₂, h₁₂, hR₂, HD⟩ := exists_fg_lbIso_of_isPullback (A₀ ⊗ A₀).hom hR₁ (B₁ ⊗ B₁).hom _
    (GlobalTheory.SymSpread.isPullback_square h₁) V.left (B' ⊗ B').hom (GlobalTheory.SymSpread.isPullback_square hψ)
    (abelian₂ B₁ L₁) (P.pull β₂₁) hΛ₁ (pull_isLB hP _) HV
  let τ : Sp R₂ ⟶ Sp R₁ := spMap (Subalgebra.inclusion h₁₂).toRingHom
  have hτ : τ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k R₂) := by
    rw [spMap_comp_ring]; rfl
  obtain ⟨B₂, _, κ, hκ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback B₁ τ
  have hB₂ : IsAbelianScheme B₂ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB₁ hκ
  haveI : IsCommMonObj B₂ := hB₂.comm
  refine ⟨R₂, hR₂, ?_⟩
  rw [← hτ, Category.assoc]
  let W := lift (pushPt hκ.1.w (fst B₂ B₂)) (pushPt hκ.1.w (snd B₂ B₂))
  have hsqW : IsSquare κ W.left := GlobalTheory.LamPull.exists_isSquare hκ.1.w
  have hL₂ : (L₁.pull κ).IsLB := pull_isLB hL₁ κ
  refine ⟨B₂, inferInstance, inferInstance, κ ≫ β₁ ≫ φ₀, W.left ≫ β₂₁, hκ.comp hc,
    GlobalTheory.ZM.SiegPull.isSquare_comp hsqW hsq₁, L₁.pull κ, hL₂, ?_⟩
  have d₁ : LBIso (abelian₂ B₂ (L₁.pull κ)) ((abelian₂ B₁ L₁).pull W.left) :=
    GlobalTheory.SymSpread.lbIso_cube hκ hL₁ hL₂ (lbIso_refl hL₂) (x2 B₁) (x2 B₂) W (fun i => by fin_cases i <;> simp [W, x2])
  have d₂ : LBIso ((abelian₂ B₁ L₁).pull W.left) ((P.pull β₂₁).pull W.left) :=
    HD _ (B₂ ⊗ B₂).hom W.left (GlobalTheory.SymSpread.isPullback_square hκ).w
  exact LBIso.trans (LB.isLB_linComb hL₂ _ _) (pull_isLB hΛ₁ _) (pull_isLB hP _) d₁
    (LBIso.trans (pull_isLB hΛ₁ _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) d₂
      (Spread.lbIso_pull_pull hP W.left rfl).symm)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalBijectiveCoefficientsPull1BijectiveStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natural_bijective_coefficients_pull1_bijective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F F' : C ⥤ CommAlgCat.{0} R) (α : ∀ T, F.obj T →+* F'.obj T) (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b)) (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b), (∀ T, Function.Bijective (α T)) → Function.Bijective (GlobalTheory.Obs.BC.natCoef α nat smul).pull1 := by
  first | exact @GlobalTheory.Obs.BC.natCoef_pull1_bijective | exact GlobalTheory.Obs.BC.natCoef_pull1_bijective | (intros; apply GlobalTheory.Obs.BC.natCoef_pull1_bijective <;> assumption)
end

