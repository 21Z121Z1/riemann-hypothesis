import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0419
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RebasedTypicalCurvesIsBasis
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

namespace GlobalTheory.DepthStages.RebaseBasis

theorem rebase_isBasis : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (G : LogFGL v d)
      (γ : Fin d → Fin d → PowerSeries C) (X : Matrix (Fin d) (Fin d) C),
      IsBasis G p ty γ → (∀ a b, IsIntV v (X a b)) → v X.det = 0 →
      (∀ a b, X a b ≠ 0 → ty b = ty a) →
      IsBasis G p ty (rebase G X γ) ∧
        (∀ a, tangent (rebase G X γ a) = ∑ b, X a b • tangent (γ b)) ∧
        ∀ a n, G.lc p (rebase G X γ a) n = ∑ b, X a b ^ (p ^ n) • G.lc p (γ b) n := by
  intro C _ _ _ v p hp hv d h ty G γ X hB hX hdet hty
  obtain ⟨hγc, hγty, hγdet⟩ := hB
  have key : ∀ a, _ := fun a => pt6' C v p hp hv d d G γ (X a) hγc (hX a)
  have hlc : ∀ a n, G.lc p (rebase G X γ a) n = ∑ b, X a b ^ (p ^ n) • G.lc p (γ b) n :=
    fun a n => (key a).2.2.1 n
  have htan : ∀ a, tangent (rebase G X γ a) = ∑ b, X a b • tangent (γ b) := fun a => (key a).2.1
  refine ⟨⟨fun a => (key a).1, fun a => ⟨(key a).2.2.2 fun b => (hγty b).1, ?_⟩, ?_⟩, htan, hlc⟩
  · intro n c hc
    rw [hlc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hXab : X a b = 0
    · rw [hXab, zero_pow (pow_ne_zero _ hp.ne_zero), zero_mul]
    · have hb := hty a b hXab
      rw [(hγty b).2 n c (by rw [hb]; exact hc), mul_zero]
  · have hM : (Matrix.of fun a b => tangent (rebase G X γ a) b) =
        X * Matrix.of fun a b => tangent (γ a) b := by
      ext a b
      rw [Matrix.of_apply, htan, Matrix.mul_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [hM, Matrix.det_mul, v.map_mul, hdet, hγdet, add_zero]

end GlobalTheory.DepthStages.RebaseBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictGlob1Bijective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem restrict_glob1_bijective : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (ω : Ω[F.obj T⁄R]), (∀ t (u : T ⟶ G.obj t), p1 F u ω = 0) → ω = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → Ω[F.obj (G.obj t)⁄R]), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 F (G.map a) (s t u)) → ∃ ω : Ω[F.obj T⁄R], ∀ t u, p1 F u ω = s t u) → Function.Bijective (pullGlob1 (CoefMap.restrict F G)) := by
  intro R _ C _ C' _ F G hsep hglue
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    apply Subtype.ext
    funext T
    refine hsep T (ω.1 T) fun t u ↦ ?_
    have h1 := congrArg (fun x : Glob1 (G ⋙ F) ↦ x.1 t) hω
    have h2 : (pullGlob1 (CoefMap.restrict F G) ω).1 t = ω.1 (G.obj t) := cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _
    rw [← ω.2 u, ← h2, h1]
    rfl
  · intro ω'
    have hc : ∀ (T : C), ∃ ω : Ω[F.obj T⁄R], ∀ t (u : T ⟶ G.obj t), p1 F u ω = ω'.1 t :=
      fun T ↦ hglue T (fun t _ ↦ ω'.1 t) fun t t' u a ↦ ω'.2 a
    choose ω hω using hc
    have hglob : ω ∈ Glob1 F := by
      intro T T' φ
      rw [← sub_eq_zero]
      refine hsep T' _ fun t u ↦ ?_
      rw [map_sub, ← oneFormsMapOfFunctorMorphism_comp, hω, hω, sub_self]
    refine ⟨⟨ω, hglob⟩, Subtype.ext (funext fun t ↦ ?_)⟩
    change q1 (CoefMap.restrict F G) t (ω (G.obj t)) = ω'.1 t
    rw [cechDeRhamCoefMapOneForms_restrictAlongFunctor, ← hω (G.obj t) t (𝟙 _), oneFormsMapOfFunctorMorphism_id]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictPull1InjectiveOfSepGlue
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.CoefMap

theorem restrict_pull1_injective_of_sep_glue {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (hsep : ∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0)
    (hglue : ∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)),
      (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) →
      ∃ x : F.obj T, ∀ t u, mp F u x = s t u) :
    Function.Injective (CoefMap.restrict F G).pull1 := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
  obtain ⟨g₀, hg⟩ := hc
  let g : ∀ t, F.obj (G.obj t) := fun t ↦ g₀ t
  have hg' : ∀ t t' (a : t ⟶ t'), g t' - mp F (G.map a) (g t) = f.1 _ _ (G.map a) := fun t t' a ↦
    congrFun (congrFun (congrFun hg t) t') a
  have h1 : ∀ T : C, ∃ x : F.obj T, ∀ t (u : T ⟶ G.obj t), mp F u x = g t - f.1 T _ u := by
    intro T
    refine hglue T (fun t u ↦ g t - f.1 T _ u) fun t t' u a ↦ ?_
    have k1 := Z1.comp f u (G.map a)
    have k2 := hg' t t' a
    simp only [map_sub]
    linear_combination k2 - k1
  choose x hx using h1
  refine H1.mk_eq_zero.2 ⟨x, ?_⟩
  funext T T' φ
  rw [amitsur_d0_apply]
  refine (sub_eq_zero.1 (hsep T' _ fun t u ↦ ?_)).symm
  have k1 := Z1.comp f φ u
  have k2 := hx T' t u
  have k3 := hx T t (φ ≫ u)
  rw [mp_comp] at k3
  simp only [map_sub]
  linear_combination k3 - k2 - k1

end GlobalTheory.CatCoh.CoefMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityEtaleLocallyPowPrimitiveRootStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootOfUnity_etaleLocally_pow_primitiveRoot : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ ω : (Γ(U, ⊤))ˣ, ω ^ q = 1 →
    Loc U fun V g => ∃ (ζ : Prim q Γ(V, ⊤)) (a : ℕ), (Units.map g.appTop.hom.toMonoidHom ω : Γ(V, ⊤)) = ζ.1 ^ a := by
  first | (exact @GlobalTheory.EtC.RootLoc.root_loc_pow_prim) | (exact GlobalTheory.EtC.RootLoc.root_loc_pow_prim) | (intros; apply GlobalTheory.EtC.RootLoc.root_loc_pow_prim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootTrickFinsetCurvesBlockInverse
section
namespace GlobalTheory.RootFin

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

open MvPowerSeries in
private lemma sum_dite_mem_eq_sum_equivFin {d : ℕ} (S : Finset (Fin d)) {M : Type*} [AddCommMonoid M] (F : S → M) :
    ∑ b, (if hb : b ∈ S then F ⟨b, hb⟩ else 0) = ∑ w : Fin S.card, F (S.equivFin.symm w) := by
  rw [Equiv.sum_comp S.equivFin.symm F,
    ← Finset.sum_subset (Finset.subset_univ S) (fun b _ hb => by simp [hb]), ← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl (fun b _ => by simp [b.2])

open MvPowerSeries in
private lemma lc_sumF_eq_sum {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d m : ℕ} (G : _root_.ReciprocityTheory.PGsh.LogFGL v d) (p : ℕ)
    (g : Fin m → Fin d → PowerSeries C) (hg : ∀ u, _root_.ReciprocityTheory.PGsh.IsCurve v (g u)) (n : ℕ) :
    G.lc p (G.sumF g) n = ∑ u, G.lc p (g u) n := by
  funext c
  simp only [_root_.ReciprocityTheory.PGsh.LogFGL.lc, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_sumF G g hg c, map_sum, Finset.sum_apply]

open MvPowerSeries in
private lemma lc_rescaleCurve_eq_pow_smul {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : _root_.ReciprocityTheory.PGsh.LogFGL v d) (p : ℕ)
    (x : C) {ga : Fin d → PowerSeries C} (hga : _root_.ReciprocityTheory.PGsh.IsCurve v ga) (n : ℕ) :
    G.lc p (_root_.ReciprocityTheory.PGsh.rescaleCurve x ga) n = x ^ (p ^ n) • G.lc p ga n := by
  funext c
  simp only [_root_.ReciprocityTheory.PGsh.LogFGL.lc, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_rescale G x (fun b => (hga b).1) c, PowerSeries.coeff_rescale, Pi.smul_apply, smul_eq_mul]

open MvPowerSeries in

theorem _root_.GlobalTheory.RootFin.root_fin : _root_.ReciprocityTheory.ChartRestriction.G.Sh.RootStatement → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (i : ZMod h) (G : _root_.ReciprocityTheory.PGsh.LogFGL v d)
      (γ : Fin d → Fin d → PowerSeries C) (S : Finset (Fin d)),
      (∀ a ∈ S, _root_.ReciprocityTheory.PGsh.IsCurve v (γ a)) → (∀ a ∈ S, G.IsOfType p ty i (γ a)) → ∀ (n j : ℕ), 1 ≤ n →
      ∀ (V : Type) [AddCommGroup V] [Module C V] (La : (Fin d → C) →ₗ[C] V),
        Module.finrank C (Submodule.span C
          ((fun a => La (G.lc p (γ a) n)) '' (S : Set (Fin d)))) ≤ j →
        ∃ (x y : Matrix (Fin d) (Fin d) C) (D : Finset (Fin d)), D ⊆ S ∧ D.card ≤ j ∧
          (∀ a b, _root_.ReciprocityTheory.PGsh.IsIntV v (x a b)) ∧ (∀ a b, _root_.ReciprocityTheory.PGsh.IsIntV v (y a b)) ∧
          (∀ a b, x a b ≠ 0 → a ∈ S ∧ b ∈ S) ∧ (∀ a b, y a b ≠ 0 → a ∈ S ∧ b ∈ S) ∧
          (∀ a c, a ∈ S → c ∈ S → ∑ b, x a b * y b c = if a = c then 1 else 0) ∧
          ∀ a ∈ S, a ∉ D → La (∑ b, x a b ^ (p ^ n) • G.lc p (γ b) n) = 0 := by
  intro hroot C _ _ _ v p hp hv d h ty i G γ S hcurve htype n j hn V _ _ La hrank
  set e : Fin S.card ≃ S := S.equivFin.symm with he
  set γS : Fin S.card → Fin d → PowerSeries C := fun u => γ (e u) with hγS
  have hcS : ∀ u, _root_.ReciprocityTheory.PGsh.IsCurve v (γS u) := fun u => hcurve _ (e u).2
  have htS : ∀ u, G.IsOfType p ty i (γS u) := fun u => htype _ (e u).2
  have hrange : Set.range (fun u => La (G.lc p (γS u) n)) = (fun a => La (G.lc p (γ a) n)) '' (S : Set (Fin d)) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨e u, (e u).2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨e.symm ⟨a, ha⟩, by simp [γS]⟩
  obtain ⟨T, hTint, hTdet, hrest⟩ := hroot C v p hp hv d h S.card ty i G γS hcS htS n j hn V La (hrange ▸ hrank)
  obtain ⟨-, -, hTzero⟩ := hrest
  have hTinv := _root_.ReciprocityTheory.ChartRestriction.G.Sh.pt_inv_int (fun a b => (_root_.ReciprocityTheory.ChartRestriction.G.Sh.ptIsIntV_iff _).mp (hTint a b)) hTdet
  have hzero : _root_.ReciprocityTheory.PGsh.IsIntV v (0 : C) := (_root_.ReciprocityTheory.ChartRestriction.G.Sh.ptIsIntV_iff _).mpr (Subring.zero_mem _)
  set x : Matrix (Fin d) (Fin d) C := fun a b =>
    if ha : a ∈ S then if hb : b ∈ S then T (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) else 0 else 0 with hx
  set y : Matrix (Fin d) (Fin d) C := fun a b =>
    if ha : a ∈ S then if hb : b ∈ S then T⁻¹ (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) else 0 else 0 with hy
  set D : Finset (Fin d) := (Finset.univ.filter (fun w : Fin S.card => (w : ℕ) < j)).image (fun w => (e w : Fin d)) with hD
  refine ⟨x, y, D, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp ha
    exact (e w).2
  · refine Finset.card_image_le.trans ?_
    calc (Finset.univ.filter (fun w : Fin S.card => (w : ℕ) < j)).card ≤ (Finset.range j).card :=
          Finset.card_le_card_of_injOn (fun w => (w : ℕ)) (fun w hw => by simpa using hw)
            (fun a _ b _ hab => Fin.ext hab)
      _ = j := Finset.card_range j
  · intro a b
    simp only [hx]
    split_ifs
    · exact hTint _ _
    · exact hzero
    · exact hzero
  · intro a b
    simp only [hy]
    split_ifs
    · exact (_root_.ReciprocityTheory.ChartRestriction.G.Sh.ptIsIntV_iff _).mpr (hTinv.2 _ _)
    · exact hzero
    · exact hzero
  · intro a b hab
    simp only [hx] at hab
    split_ifs at hab with ha hb
    · exact ⟨ha, hb⟩
    · exact absurd rfl hab
    · exact absurd rfl hab
  · intro a b hab
    simp only [hy] at hab
    split_ifs at hab with ha hb
    · exact ⟨ha, hb⟩
    · exact absurd rfl hab
    · exact absurd rfl hab
  · intro a c ha hc
    have hterm : ∀ b, x a b * y b c = if hb : b ∈ S then
        T (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) * T⁻¹ (e.symm ⟨b, hb⟩) (e.symm ⟨c, hc⟩) else 0 := by
      intro b
      simp only [hx, hy, dif_pos ha, dif_pos hc]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun b _ => hterm b),
      sum_dite_mem_eq_sum_equivFin S (fun b : S => T (e.symm ⟨a, ha⟩) (e.symm b) * T⁻¹ (e.symm b) (e.symm ⟨c, hc⟩))]
    simp only [← he, Equiv.symm_apply_apply]
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hTinv.1, Matrix.one_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
  · intro a ha haD
    set w := e.symm ⟨a, ha⟩ with hw
    have hjw : j ≤ (w : ℕ) := by
      by_contra hlt
      push_neg at hlt
      exact haD (Finset.mem_image.mpr ⟨w, by simp [hlt], by simp [hw]⟩)
    have key := hTzero w hjw
    have hp0 : p ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hterm : ∀ b, x a b ^ (p ^ n) • G.lc p (γ b) n = if hb : b ∈ S then
        T w (e.symm ⟨b, hb⟩) ^ (p ^ n) • G.lc p (γ b) n else 0 := by
      intro b
      simp only [hx, dif_pos ha, ← hw]
      split_ifs <;> simp [zero_pow hp0]
    rw [Finset.sum_congr rfl (fun b _ => hterm b),
      sum_dite_mem_eq_sum_equivFin S (fun b : S => T w (e.symm b) ^ (p ^ n) • G.lc p (γ b) n)]
    simp only [← he, Equiv.symm_apply_apply]
    rw [lc_sumF_eq_sum G p _ (fun u => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.isCurve_rescale (hTint w u) (hcS u))] at key
    rw [Finset.sum_congr rfl (fun u _ => lc_rescaleCurve_eq_pow_smul G p (T w u) (hcS u) n)] at key
    exact key

end GlobalTheory.RootFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullA
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CechDR.AffLoc

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

abbrev TT (s : X ⟶ Sp R) : Type 1 := (IsTriv s).FullSubcategory

theorem π_bij (T : TT s) : Function.Bijective T.obj.π := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ ?_, T.obj.surj⟩
  have h := (T.obj.ker b).1 hb
  rw [T.property] at h
  exact Ideal.mem_bot.1 h

def πe (T : TT s) : T.obj.B ≃+* T.obj.B₀ := RingEquiv.ofBijective T.obj.π (π_bij T)

def pt (T : TT s) : Sp T.obj.B ⟶ X := spMap ((πe T).symm : T.obj.B₀ →+* T.obj.B) ≫ T.obj.x

theorem pt_w (T : TT s) : pt T ≫ s = algStr R T.obj.B := by
  rw [pt, Category.assoc, T.obj.w, ← spMap_comp]
  congr 1
  ext r
  exact (πe T).symm_apply_apply (algebraMap R T.obj.B r)

abbrev affF (s : X ⟶ Sp R) : AffOp X ⥤ TT s :=
  ptFunctor (F := OAff s) (fun U ↦ affPt s U.unop) (fun U ↦ affPt_w s U.unop)
    fun _ _ a ↦ affPt_res s (leOfHom a.unop)

abbrev thk (T : TT s) (p : Pair (pt T)) : TT s :=
  ⟨Thick.triv (Sec (algStr R T.obj.B) p.1.1.1) (affPt _ p.1.1 ≫ pt T)
    (by rw [Category.assoc, pt_w]; exact affPt_w _ p.1.1), rfl⟩

def secPullA (T : TT s) (p : Pair (pt T)) : Sec s p.1.2.1 →ₐ[R] Sec (algStr R T.obj.B) p.1.1.1 :=
  { secPull s (algStr R T.obj.B) p with
    commutes' := (semiHom_secPull (σ := RingHom.id R)
      (by rw [spMap_id, Category.comp_id, pt_w]) p).map_algebraMap }

def aM (T : TT s) (p : Pair (pt T)) : (affF s).obj (op p.1.2) ⟶ thk T p :=
  ⟨Thick.trivHom (T := (thk T p).obj) (secPullA T p) (secPull_affPt s _ p)⟩

theorem bM_pt (T : TT s) (p : Pair (pt T)) :
    spMap ((toSec R T.obj.B p.1.1).toRingHom.comp ((πe T).symm : T.obj.B₀ →+* T.obj.B)) =
      affPt (algStr R T.obj.B) p.1.1 ≫ spMap ((πe T).symm : T.obj.B₀ →+* T.obj.B) := by
  rw [spMap_comp, affPt_eq]
  rfl

abbrev fv (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) {T T' : TT s} (a : T ⟶ T') : T'.obj.B := f.1 T T' a

def bM (T : TT s) (p : Pair (pt T)) : T ⟶ thk T p :=
  ⟨{ φ := toSec R T.obj.B p.1.1
     φ₀ := (toSec R T.obj.B p.1.1).toRingHom.comp ((πe T).symm : T.obj.B₀ →+* T.obj.B)
     comm := fun b ↦ congrArg (toSec R T.obj.B p.1.1) ((πe T).symm_apply_apply b)
     dp := isDPMorphism_of_eq_bot _ T.property _ _
     pt := (congrArg (· ≫ T.obj.x) (bM_pt T p)).trans (Category.assoc _ _ _) }⟩

def hSec (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)) (T : TT s) (p : Pair (pt T)) :
    Sec (algStr R T.obj.B) p.1.1.1 :=
  secPullA T p (g (op p.1.2)) + fv f (aM T p) - fv f (bM T p)

end GlobalTheory.CechDR.AffLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullSurjectiveAndKer
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechDR

namespace GlobalTheory.CechDR

private theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

private theorem spi {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem secPull_surjective_and_ker (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ X : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (hpb : IsPullback i s₀ s (spMap π))
    (p : Pair i) (hp : i ⁻¹ᵁ p.1.2.1 = p.1.1.1) :
    Function.Surjective (secPull s s₀ p) ∧
      ∀ b, secPull s s₀ p b = 0 ↔ b ∈ I.map (algebraMap R (Sec s p.1.2.1)) := by
  set J : Ideal (Sec s p.1.2.1) := I.map (algebraMap R (Sec s p.1.2.1)) with hJ
  let q := Ideal.Quotient.mk J
  have hφ : ∀ r, secPull s s₀ p (algebraMap R _ r) = algebraMap R₀ _ (π r) :=
    (semiHom_secPull hpb.w p).map_algebraMap
  have hJker : ∀ a ∈ J, secPull s s₀ p a = 0 := by
    have : J ≤ RingHom.ker (secPull s s₀ p) := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro r hr
      rw [← hk, RingHom.mem_ker] at hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hφ, hr, map_zero]
    exact fun a ha ↦ this ha
  let τ : R₀ →+* (Sec s p.1.2.1 ⧸ J) := π.liftOfSurjective hπ
    ⟨q.comp (algebraMap R _), fun r hr ↦ by
      rw [hk] at hr
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)⟩
  have hτ : τ.comp π = q.comp (algebraMap R _) := RingHom.liftOfSurjective_comp _ _ _
  have hz : (spMap q ≫ affPt s p.1.2) ≫ s = spMap τ ≫ spMap π := by
    rw [Category.assoc, affPt_w, ← spc, ← spc, hτ]
  let w := hpb.lift _ _ hz
  have hw : w ≫ i = spMap q ≫ affPt s p.1.2 := hpb.lift_fst _ _ _
  haveI : IsOpenImmersion (affPt s₀ p.1.1) := p.1.1.2.isOpenImmersion_fromSpec
  haveI : IsOpenImmersion (affPt s p.1.2) := p.1.2.2.isOpenImmersion_fromSpec
  have hr : Set.range w ⊆ Set.range (affPt s₀ p.1.1) := by
    rintro _ ⟨x, rfl⟩
    have e : Set.range (affPt s₀ p.1.1) = p.1.1.1 := p.1.1.2.range_fromSpec
    have e' : Set.range (affPt s p.1.2) = p.1.2.1 := p.1.2.2.range_fromSpec
    rw [e, ← hp]
    change i (w x) ∈ (p.1.2.1 : Set X)
    rw [← e', ← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let w' := IsOpenImmersion.lift (affPt s₀ p.1.1) w hr
  have hw' : w' ≫ affPt s₀ p.1.1 = w := IsOpenImmersion.lift_fac _ _ _
  let ψ : Sec s₀ p.1.1.1 →+* (Sec s p.1.2.1 ⧸ J) := (Spec.preimage w').hom
  have hψ : spMap ψ = w' := Spec.map_preimage w'
  have h1 : ψ.comp (secPull s s₀ p) = q := by
    apply spi
    rw [← cancel_mono (affPt s p.1.2), spc, Category.assoc, secPull_affPt, hψ, ← Category.assoc,
      hw', hw]
  let ψ' := Ideal.Quotient.lift J (secPull s s₀ p) hJker
  have h2 : ψ'.comp q = secPull s s₀ p := Ideal.Quotient.lift_comp_mk _ _ _
  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback hpb.flip this
  haveI : Mono (spMap (secPull s s₀ p) ≫ affPt s p.1.2) := by
    rw [secPull_affPt]; infer_instance
  haveI : Mono (spMap (secPull s s₀ p)) := mono_of_mono _ (affPt s p.1.2)
  have h3 : ψ'.comp ψ = RingHom.id _ := by
    apply spi
    rw [← cancel_mono (spMap (secPull s s₀ p)), ← spc, ← spc, RingHom.comp_assoc, h1, h2,
      RingHom.id_comp]
  refine ⟨fun b ↦ ?_, fun b ↦ ⟨fun hb ↦ ?_, hJker b⟩⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ b)
    refine ⟨a, ?_⟩
    rw [← h2, RingHom.comp_apply, show q a = ψ b from ha]
    exact congrArg (fun f ↦ f b) h3
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q b = 0
    rw [← h1, RingHom.comp_apply, hb, map_zero]

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionwiseTensorPresheafLocallyBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionwiseTensor_presheaf_locallyBijective : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 := by
  first | (exact @GlobalTheory.EtC.tensor_loc_bij) | (exact GlobalTheory.EtC.tensor_loc_bij) | (intros; apply GlobalTheory.EtC.tensor_loc_bij  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepOfFactoringCover
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory

theorem sep_of_factoring_cover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) := by
  intro R _ C _ C' _ F G H hcov T x hx
  obtain ⟨n, b, hb, h⟩ := hcov T
  refine Desc.sep_std H hb x fun S u ⟨i, hi⟩ ↦ ?_
  obtain ⟨t, v, w, rfl⟩ := h i S u hi
  rw [mp_comp, hx t v, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexSemilinearMapCompBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J J' : Cx R} (ρ : SemiMap I J) (ρ' : SemiMap I J') (u : J ⟶ J'), (∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U), ρ'.app U s a = Sec.map (u.f s) (ρ.app U s a)) → (∀ (E : Spc) (n : ℤ) x, ρ'.op.app E n x = cpush _ u n (ρ.op.app E n x)) ∧ ((∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) → ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n)) := by
  first | (exact @GlobalTheory.EtC.OpComp.op_comp_bij) | (exact GlobalTheory.EtC.OpComp.op_comp_bij) | (intros; apply GlobalTheory.EtC.OpComp.op_comp_bij  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquivStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_mappingCone_resolution_homotopyEquiv : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact → ∃ e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃), Nonempty (Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g)) := by
  first | (exact @GlobalTheory.EtC.cone_resMap_homotopyEquiv) | (exact GlobalTheory.EtC.cone_resMap_homotopyEquiv) | (intros; apply GlobalTheory.EtC.cone_resMap_homotopyEquiv  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicWeylElementGenerateUnitary
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem mem_of_inCell {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
    {ν : Type} [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E)))
    (hP : sieg c ν ≤ U) (hw : weyl c ν ∈ U) {g : UG c (stdJ ν E)} (hg : InCell c g) : g ∈ U := by
  obtain ⟨p, hp, q, hq, rfl⟩ := hg
  exact U.mul_mem (U.mul_mem (hP hp) hw) (hP hq)

theorem sieg_weyl_generate : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
    (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))),
    sieg c ν ≤ U → weyl c ν ∈ U → U = ⊤ := by
  intro F _ _ E _ _ c δ hE ν _ _ U hP hw
  classical
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_translate_inCell' F E c δ hE ν {1, g}
  have h1 : u ∈ U := by
    simpa using mem_of_inCell c U hP hw (hu 1 (by simp))
  have h2 : g * u ∈ U := mem_of_inCell c U hP hw (hu g (by simp))
  simpa using U.mul_mem h2 (U.inv_mem h1)

end GlobalTheory.KSp
end

