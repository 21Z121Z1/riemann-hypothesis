import Development.EtaleCohomology.WeilConjectures.Bundle0001
import Development.EtaleCohomology.KummerTheory.Bundle0005
import Mathlib.NumberTheory.Padics.ProperSpace
import Development.EtaleCohomology.WeilConjectures.FermatCount
import Development.EtaleCohomology.WeilConjectures.ArtinCut

-- bundled from Development.EtaleCohomology.WeilConjectures.AbsContPf
section
namespace LateralTheory.EWeil.AbsContPf

universe u v

open LateralTheory.EWeil.ContinCut

namespace AbsoluteContinuitySecondLemma

theorem goal1 (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (q : ℚ_[l]) : ‖a • q‖ = ‖a‖ * ‖q‖ := by
  rw [Algebra.smul_def, norm_mul]; rfl

end AbsoluteContinuitySecondLemma

theorem norm_smul_le (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (q : ℚ_[l]) : ‖a • q‖ = ‖a‖ * ‖q‖ :=
  AbsoluteContinuitySecondLemma.goal1 l a q

namespace AbsoluteContinuityFirstLemma

namespace AbsoluteContinuitySmulBound

private lemma smul_bound (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (q : ℚ_[l]) : ‖a • q‖ ≤ ‖q‖ := by
  rw [Algebra.smul_def, norm_mul]
  have h : ‖(algebraMap ℤ_[l] ℚ_[l] a)‖ ≤ 1 := by
    have e : algebraMap ℤ_[l] ℚ_[l] a = (a : ℚ_[l]) := rfl
    rw [e, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one a
  calc ‖algebraMap ℤ_[l] ℚ_[l] a‖ * ‖q‖ ≤ 1 * ‖q‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖q‖ := one_mul _

end AbsoluteContinuitySmulBound

theorem goal1 (l : ℕ) [Fact l.Prime] (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
    (φ : M →ₗ[ℤ_[l]] ℚ_[l]) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖φ m‖ ≤ C := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] M).FG)
  refine ⟨∑ x ∈ s, ‖φ x‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro m
  have hm : m ∈ Submodule.span ℤ_[l] (s : Set M) := by rw [hs]; trivial
  induction hm using Submodule.span_induction with
  | mem x hx =>
      exact Finset.single_le_sum (f := fun x => ‖φ x‖) (fun _ _ => norm_nonneg _) hx
  | zero => simpa using Finset.sum_nonneg (fun (x : M) (_ : x ∈ s) => norm_nonneg (φ x))
  | add x y _ _ hx hy =>
      rw [map_add]
      exact (Padic.nonarchimedean _ _).trans (max_le hx hy)
  | smul a x _ hx =>
      rw [map_smul]
      exact (AbsoluteContinuitySmulBound.smul_bound l a (φ x)).trans hx

end AbsoluteContinuityFirstLemma

theorem bdd (l : ℕ) [Fact l.Prime] (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
    (φ : M →ₗ[ℤ_[l]] ℚ_[l]) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖φ m‖ ≤ C :=
  AbsoluteContinuityFirstLemma.goal1 l M φ

theorem AbsCont_of (hC : Chev.{u}) : AbsCont.{u, v} := by
  intro l _ G _ _ _ M _ _ _ ρ K hK h0 hopen φ x
  obtain ⟨C, hC0, hCb⟩ := bdd l M φ
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : (0 : ℝ) < l := by linarith
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0:ℝ) < C + 1))
    (inv_lt_one_of_one_lt₀ hl1)
  obtain ⟨k, hk⟩ := hC l M K hK h0 N
  set y := ρ g₀ x
  have hU : IsOpen {g : G | g * g₀⁻¹ ∈ {h : G | ρ h y - y ∈ K k}} :=
    (hopen y k).preimage (continuous_id.mul continuous_const)
  have hmem : g₀ ∈ {g : G | g * g₀⁻¹ ∈ {h : G | ρ h y - y ∈ K k}} := by
    simp [y]
  filter_upwards [hU.mem_nhds hmem] with g hg
  change ρ (g * g₀⁻¹) y - y ∈ K k at hg
  have hd : ρ g x - ρ g₀ x ∈ K k := by
    have : ρ (g * g₀⁻¹) y = ρ g x := by
      simp only [y]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [this] at hg; exact hg
  obtain ⟨z, hz⟩ := hk _ hd
  rw [dist_eq_norm, ← map_sub, hz, map_smul, norm_smul_le, PadicInt.norm_p_pow]
  have hzC := hCb z
  have hpow : (l : ℝ) ^ (-(N : ℤ)) = (l : ℝ)⁻¹ ^ N := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hpow]
  have hp0 : 0 ≤ (l : ℝ)⁻¹ ^ N := by positivity
  calc (l : ℝ)⁻¹ ^ N * ‖φ z‖ ≤ (l : ℝ)⁻¹ ^ N * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hp0
    _ < ε / (C + 1) * (C + 1) := mul_lt_mul_of_pos_right hN (by linarith)
    _ = ε := div_mul_cancel₀ _ (by linarith)

end LateralTheory.EWeil.AbsContPf
end

-- bundled from Development.EtaleCohomology.WeilConjectures.AdicKerPf
section
noncomputable section
open CategoryTheory Opposite GlobalTheory.EtC LateralTheory.KummerTheory

namespace LateralTheory.EWeil.AdicKerPf

theorem nz (l : ℕ) [Fact l.Prime] (k : ℕ) : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem comp (hA : A11) {l : ℕ} [Fact l.Prime] {E : Spc} {n i : ℤ} (y : Hl l E n i) (M m : ℕ) (h : m ≤ M) :
    red (l ^ M) (l ^ m) E n i (y.1 M) = y.1 m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => haveI := nz l m; exact (hA (l ^ m) (l ^ m) dvd_rfl E).2.2.1 n i (y.1 m)
  | succ d ih =>
    haveI := nz l (m + (d + 1))
    rw [← (hA (l ^ (m + (d + 1))) (l ^ (m + d)) (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ m)
      (pow_dvd_pow l (by omega)) n i (y.1 _)]
    rw [show red (l ^ (m + (d + 1))) (l ^ (m + d)) E n i (y.1 (m + (d + 1))) = y.1 (m + d) from y.2 (m + d)]
    exact ih

theorem smul_pow {l : ℕ} [Fact l.Prime] {E : Spc} {n i : ℤ} (m b : ℕ) (v : HtL l m E n i) :
    ((l : ℤ_[l]) ^ b) • v = (show Ht (l ^ m) E n i from (l ^ b : ℕ) • v) := by
  change PadicInt.toZModPow m ((l : ℤ_[l]) ^ b) • (show Ht (l ^ m) E n i from v) = _
  rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rfl

theorem AdicKer_of : LateralTheory.KummerTheory.AdicKer := by
  intro hA l _ E i hB hFin n b x hx
  change x.1 b = 0 at hx
  obtain ⟨u, d, hBk⟩ := hB b
  let S : ℕ → Type 1 := fun a => {w : Ht (l ^ a) E n i // u a n w = x.1 (b + a)}
  let f : ∀ a, S (a + 1) → S a := fun a w => ⟨red (l ^ (a + 1)) (l ^ a) E n i w.1, by
    rw [← (hBk a n).2.2.2.2.2 w.1, w.2]; exact x.2 (b + a)⟩
  let F : ℕᵒᵖ ⥤ Type 1 := Functor.ofOpSequence (X := S) fun a => TypeCat.ofHom (f a)
  haveI : ∀ j, Finite (F.obj j) := fun j => by
    haveI := hFin j.unop n
    exact (inferInstance : Finite (S j.unop))
  haveI : ∀ j, Nonempty (F.obj j) := fun j => by
    have h0 : red (l ^ (b + j.unop)) (l ^ b) E n i (x.1 (b + j.unop)) = 0 := by
      rw [comp hA x (b + j.unop) b (by omega)]; exact hx
    obtain ⟨w, hw⟩ := ((hBk j.unop n).1 (x.1 (b + j.unop))).1 h0
    exact ⟨(⟨w, hw⟩ : S j.unop)⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  let y : Hl l E n i := ⟨fun a => (show S a from s (op a)).1, fun a => by
    have := hs (homOfLE (Nat.le_succ a)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at this
    exact congrArg Subtype.val this⟩
  refine ⟨y, Subtype.ext (funext fun m => ?_)⟩
  change x.1 m = ((l : ℤ_[l]) ^ b) • y.1 m
  rw [smul_pow]
  rcases le_or_gt m b with h | h
  · have hxm : x.1 m = 0 := by
      rw [← comp hA x b m h]
      exact (congrArg (red (l ^ b) (l ^ m) E n i) hx).trans (map_zero _)
    rw [hxm]
    obtain ⟨c, hc⟩ := pow_dvd_pow l h
    change 0 = (l ^ b : ℕ) • (show Ht (l ^ m) E n i from y.1 m)
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ m)), hc, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_smul]
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h.le
    have h1 : u a n (y.1 a) = x.1 (b + a) := (show S a from s (op a)).2
    rw [← h1, ← comp hA y (b + a) a (by omega)]
    exact (hBk a n).2.2.2.1 (y.1 (b + a))

end LateralTheory.EWeil.AdicKerPf
end
end

-- bundled from Development.EtaleCohomology.WeilConjectures.ChevPf
section
namespace LateralTheory.EWeil.ChevPf

open Topology

theorem Chev_of : LateralTheory.EWeil.ContinCut.Chev := by
  intro l _ M _ _ _ K hK h0 N
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] M
  let V : ℕ → Set (Fin r → ℤ_[l]) := fun k => ((K k).comap π : Set (Fin r → ℤ_[l]))
  have hc : ∀ k, IsCompact (V k) := by
    intro k
    obtain ⟨s, g, hg⟩ := Module.Finite.exists_fin' ℤ_[l] ((K k).comap π)
    have : V k = Set.range (((K k).comap π).subtype.comp g) := by
      ext z
      constructor
      · intro hz
        obtain ⟨a, ha⟩ := hg ⟨z, hz⟩
        exact ⟨a, by simp [ha]⟩
      · rintro ⟨a, rfl⟩
        exact (g a).2
    rw [this]
    exact isCompact_range (LinearMap.continuous_on_pi _)
  have hdir : Directed (· ⊇ ·) V := by
    intro a b
    refine ⟨max a b, ?_, ?_⟩
    · intro z hz; exact hK (le_max_left a b) hz
    · intro z hz; exact hK (le_max_right a b) hz
  let ε : ℝ := (l : ℝ) ^ (-(N : ℤ))
  have hε : 0 < ε := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  let U : Set (Fin r → ℤ_[l]) :=
    {z | ∃ c w, π c = 0 ∧ (∀ i, ‖w i‖ ≤ ε) ∧ z = c + w}
  have hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x := by
    intro x hx
    have hx0 : π x = 0 := h0 _ (fun k => Set.mem_iInter.1 hx k)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x hε) ?_
    intro z hz
    refine ⟨x, z - x, hx0, fun i => ?_, by abel⟩
    have h1 : dist (z i) (x i) ≤ dist z x := dist_le_pi_dist z x i
    rw [Metric.mem_ball] at hz
    rw [Pi.sub_apply, ← dist_eq_norm]
    linarith
  obtain ⟨k, hk⟩ := exists_subset_nhds_of_isCompact hdir hc hU
  refine ⟨k, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := hπ y
  obtain ⟨c, w, hc0, hw, rfl⟩ := hk (show x ∈ V k from hy)
  have hu : ∀ i, ∃ u : ℤ_[l], w i = (l : ℤ_[l]) ^ N * u := by
    intro i
    have := (PadicInt.norm_le_pow_iff_mem_span_pow (w i) N).1 (hw i)
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨u, by rw [← hu, mul_comm]⟩
  choose u hu using hu
  refine ⟨π u, ?_⟩
  have : w = (l : ℤ_[l]) ^ N • u := funext fun i => by simp [hu i]
  rw [map_add, hc0, zero_add, this, map_smul]

end LateralTheory.EWeil.ChevPf
end

-- bundled from Development.EtaleCohomology.WeilConjectures.FinQCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.FinQCut

theorem inv_of_over {q : ℕ} {A : Type} [CommRing A] (hq : IsUnit (q : A)) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of A)) : Inv q (sch.obj X) := by
  rintro U ⟨x⟩
  have f : U ⟶ X := x
  have h := hq.map (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (f ≫ p).appTop).hom)
  rwa [map_natCast] at h

end LateralTheory.EWeil.FinQCut

end
end

-- bundled from Development.EtaleCohomology.WeilConjectures.GluePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.Gys.LV.GluePf
open LateralTheory.EWeil LateralTheory.EWeil.Gys LateralTheory.EWeil.Gys.LV

def Sig : Prop := ∀ (l r : ℕ) (P : SPair l r) {T : Type} (Q : T → SPair l r) (g : ∀ t, (Q t).Hom P),
  ∃ (P' : SPair l r) (f : P'.Hom P) (a : ∀ t, (Q t).Hom P'), (∀ t, (a t).fX ≫ f.fX = (g t).fX) ∧
    Nonempty (IsColimit (Cofan.mk P'.X fun t => (a t).fX)) ∧ Nonempty (IsColimit (Cofan.mk P'.U fun t => (a t).fU)) ∧
    ((∀ x : P.X, ∃ t, x ∈ Set.range (g t).fX) → Surjective f.fX)

def ShvSigma : Prop := ∀ (R : Type) [CommRing R] (F : GlobalTheory.EtC.Shv R) {T : Type} {Y : T → Scheme.{0}} (c : Cofan Y), IsColimit c →
  Function.Bijective (fun (s : GlobalTheory.EtC.Sec F c.pt) (t : T) => GlobalTheory.EtC.Sec.res (c.inj t) s)

theorem glue_of (hS : Sig) (hF : ShvSigma) : Glue := by
  intro l _ r P c i n x hx
  choose Q g ht hz using hx
  obtain ⟨P', f, a, hfa, ⟨hX⟩, ⟨hU⟩, hsurj⟩ := hS l r P Q g
  refine ⟨P', f, hsurj fun t => ⟨t, ht t⟩, ?_⟩
  induction x using QuotientAddGroup.induction_on with
  | H z => ?_
  have key : ∀ t, ∃ y : SecI (l ^ c) i (Q t).X (n - 1), resA (l ^ c) i (Q t).j (n - 1) y = 0 ∧
      dA (l ^ c) i (Q t).X (n - 1) n y = resA (l ^ c) i (g t).fX n z.1 := by
    intro t
    have h := hz t
    unfold pullZ at h
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h
    obtain ⟨y, hy, e⟩ := h
    exact ⟨y, hy, e⟩
  choose y hy hd using key
  obtain ⟨Y, hY⟩ := (hF _ ((res _ (tw (l ^ c) i)).X (n - 1)) _ hX).2 y
  have hYt : ∀ t, resA (l ^ c) i (a t).fX (n - 1) Y = y t := fun t => congrFun hY t
  unfold pullZ
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  refine ⟨Y, ?_, ?_⟩
  · show resA (l ^ c) i P'.j (n - 1) Y = 0
    apply (hF _ ((res _ (tw (l ^ c) i)).X (n - 1)) _ hU).1
    funext t
    change resA (l ^ c) i (a t).fU (n - 1) (resA (l ^ c) i P'.j (n - 1) Y) = resA (l ^ c) i (a t).fU (n - 1) 0
    rw [map_zero, ← resA_comp, (a t).sqU, resA_comp, hYt, hy]
  · show dA (l ^ c) i P'.X (n - 1) n Y = resA (l ^ c) i f.fX n z.1
    apply (hF _ ((res _ (tw (l ^ c) i)).X n) _ hX).1
    funext t
    change resA (l ^ c) i (a t).fX n (dA (l ^ c) i P'.X (n - 1) n Y) = resA (l ^ c) i (a t).fX n (resA (l ^ c) i f.fX n z.1)
    rw [resA_dA, hYt, hd, ← resA_comp, hfa]

end LateralTheory.EWeil.Gys.LV.GluePf
end
end

-- bundled from Development.EtaleCohomology.WeilConjectures.LerayCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.t_E3Cut (Et IE SHExists IEComp pC)
open LateralTheory.EWeil.ArtinCut

namespace LateralTheory.EWeil.LerayCut

universe u v w

abbrev gam {C : Type u} [Category.{v} C] [Preadditive C] (U : C) : C ⥤ AddCommGrpCat.{v} :=
  preadditiveCoyoneda.obj (op U)

abbrev gamCx {C : Type u} [Category.{v} C] [Preadditive C] (U : C) (K : CochainComplex C ℕ) :
    CochainComplex AddCommGrpCat.{v} ℕ :=
  ((gam U).mapHomologicalComplex _).obj K

abbrev unitSh (A : CommRingCat.{0}) : Sm A :=
  (constantSheaf (Spec A).smallEtaleTopology AddCommGrpCat.{1}).obj (AddCommGrpCat.of (ULift ℤ))

def Hyper : Prop := ∀ (C : Type u) [Category.{v} C] [Abelian C] [HasExt.{w} C] (U : C) (K : CochainComplex C ℕ) (d : ℕ),
  (∀ s n : ℕ, 0 < n → Subsingleton (Abelian.Ext U (K.X s) n)) →
  (∀ j m : ℕ, d < j + m → Subsingleton (Abelian.Ext U (K.homology m) j)) →
  ∀ n : ℕ, d < n → Subsingleton ((gamCx U K).homology n)

def ZeroSheaf : Prop := ∀ (A : CommRingCat.{0}) (F : Sm A), (∀ p : PrimeSpectrum A, StalkZero F p) →
  ∀ n : ℕ, Subsingleton (Sheaf.H.{1} F n)

def Push : Prop := Base → ∀ (q : ℕ) [NeZero q] {A B : CommRingCat.{0}} (β : A ⟶ B), IsUnit (q : A) → ∀ i : ℤ,
  ∃ K : CochainComplex (Sm A) ℕ,
    (∀ s n : ℕ, 0 < n → Subsingleton (Sheaf.H.{1} (K.X s) n)) ∧
    (∀ (m : ℕ) (V : (Spec A).Etale) (x : (K.homology m).obj.obj (op V)), q • x = 0) ∧
    (∀ (p : PrimeSpectrum A) (m : ℕ), (∀ (S D : CommRingCat.{0}) (f : A ⟶ S) (u : B ⟶ D) (v : S ⟶ D),
        IsStalk f p → IsPushout β f u v → Van q D m) → StalkZero (K.homology m) p) ∧
    ∀ n : ℕ, Nonempty (Ht q (sch.obj (Spec B)) n i ≃ (gamCx (unitSh A) K).homology n)

example (A : CommRingCat.{0}) (F : Sm A) (n : ℕ) : Sheaf.H.{1} F n = Abelian.Ext (unitSh A) F n := rfl

lemma enat_lt_add_of_sub_lt (d m : ℕ) (x : ℕ∞) (hm : m ≤ d) (h : ((d - m : ℕ) : ℕ∞) < x) : (d : ℕ∞) < (m : ℕ∞) + x := by
  induction x using ENat.recTopCoe with
  | top => simp
  | coe x =>
    have : d - m < x := by exact_mod_cast h
    exact_mod_cast (by omega : d < m + x)

lemma enat_lt_add_of_lt (d m : ℕ) (x : ℕ∞) (hm : d < m) : (d : ℕ∞) < (m : ℕ∞) + x :=
  lt_of_lt_of_le (by exact_mod_cast hm) le_self_add

theorem goal_of (hH : Hyper.{2, 1, 1}) (hZ : ZeroSheaf) (hP : Push) : LateralTheory.EWeil.ArtinCut.Leray := by
  intro base q _ A B β hq δ d hsm hst n hn i
  obtain ⟨K, hacy, htor, hstalk, hiso⟩ := hP base q β hq i
  have hn0 : (0 : ℤ) ≤ n := by omega
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
  have hdN : d < N := by omega
  obtain ⟨e⟩ := hiso N
  have key : Subsingleton ((gamCx (unitSh A) K).homology N) := by
    refine hH (Sm A) (unitSh A) K d (fun s k hk => hacy s k hk) ?_ N hdN
    intro j m hjm
    by_cases hm : m ≤ d
    · refine hsm (K.homology m) (htor m) (d - m) ?_ j (by omega)
      intro p hp
      exact hstalk p m (fun S D f u v hf hpo => hst p S D f u v hf hpo m (enat_lt_add_of_sub_lt d m _ hm hp))
    · refine hZ A (K.homology m) (fun p => ?_) j
      exact hstalk p m (fun S D f u v hf hpo => hst p S D f u v hf hpo m (enat_lt_add_of_lt d m _ (by omega)))
  exact e.subsingleton

end LateralTheory.EWeil.LerayCut
end
end

-- bundled from Development.EtaleCohomology.WeilConjectures.StabPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.StabPf

section Proj
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) {X : Scheme.{0}} (p : X ⟶ Sp K)

def proj : geom Ω p ⟶ geom L p :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap L Ω))) (by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    congr 3)

theorem galMap_proj (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ L.fixingSubgroup) : galMap Ω p σ ≫ proj L p = proj L p := by
  apply pullback.hom_ext
  · simp only [proj, Category.assoc, pullback.lift_fst, galMap_fst]
  · simp only [proj, Category.assoc, pullback.lift_snd]
    rw [galMap_snd_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext x
    exact (mem_fixingSubgroup_iff _).1 hσ x x.2

end Proj

def Desc : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K], (l : K) ≠ 0 →
  ∀ {X : Scheme.{0}} (p : X ⟶ Sp K), IsProper p → ∀ (n : ℤ) (k : ℕ)
    (y : HtL l k (sch.obj (geom (AlgebraicClosure K) p)) n 0),
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K L)
      (z : HtL l k (sch.obj (geom L p)) n 0), pull _ (sch.map (proj L p)) _ n z = y

end LateralTheory.EWeil.StabPf
end
end

