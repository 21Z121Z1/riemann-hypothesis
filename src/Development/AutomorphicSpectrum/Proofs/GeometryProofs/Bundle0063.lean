import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0046
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0048
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0059
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VbPull

theorem dual_frame_ext {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') {W W' : Type} [AddCommGroup W] [Module Ω W]
    [AddCommGroup W'] [Module Ω' W'] (j : W →+ W') (hj : ∀ (a : Ω) (e : W), j (a • e) = i a • j e)
    (hs : Submodule.span Ω' (Set.range j) = ⊤) (jW : Module.Dual Ω W →+ Module.Dual Ω' W')
    (hjW : ∀ u e, jW u (j e) = i (u e)) {r : ℕ} (b : Fin r → Module.Dual Ω W) (hli : LinearIndependent Ω b)
    (hb : Submodule.span Ω (Set.range b) = ⊤) :
    LinearIndependent Ω' (fun k => jW (b k)) ∧ Submodule.span Ω' (Set.range fun k => jW (b k)) = ⊤ := by
  classical
  let c := Module.Basis.mk hli hb.ge
  have hc : ∀ k, c k = b k := fun k => by simp [c]
  haveI : Module.Finite Ω (Module.Dual Ω W) := Module.Finite.of_basis c
  haveI : Module.Finite Ω W := (Module.finite_dual_iff Ω).1 inferInstance
  let e : Fin r → W := fun l => (Module.evalEquiv Ω W).symm (c.dualBasis l)
  have he : ∀ k l, b k (e l) = if k = l then 1 else 0 := by
    intro k l
    simp only [e]
    rw [Module.apply_evalEquiv_symm_apply, ← hc k, Module.Basis.dualBasis_apply_self]
  have hx : ∀ x : W, x = ∑ k, b k x • e k := by
    intro x
    rw [← sub_eq_zero]
    apply (Module.forall_dual_apply_eq_zero_iff Ω _).1
    intro u
    have hu : u ∈ Submodule.span Ω (Set.range b) := by rw [hb]; trivial
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      simp [he, map_sum]
    | zero => simp
    | add y z _ _ hy hz => simp only [LinearMap.add_apply, hy, hz, add_zero]
    | smul a y _ hy => simp only [LinearMap.smul_apply, hy, smul_zero]
  have hjx : ∀ x, j x = ∑ k, i (b k x) • j (e k) := by
    intro x
    conv_lhs => rw [hx x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hj _ _
  have hext : ∀ v v' : Module.Dual Ω' W', (∀ k, v (j (e k)) = v' (j (e k))) → v = v' := by
    intro v v' h
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨x, rfl⟩
    rw [hjx x]
    simp only [map_sum, map_smul, h]
  have hpair : ∀ k l, jW (b k) (j (e l)) = if k = l then 1 else 0 := by
    intro k l
    rw [hjW, he]
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg l
    have := congrArg (fun v : Module.Dual Ω' W' => v (j (e l))) hg
    simpa [hpair] using this
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ k, v (j (e k)) • jW (b k) := by
      apply hext
      intro l
      simp [hpair]
    rw [hv]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem isVBOn_dual_pull : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (Lo : Lat ξ (Module.Dual Ω V)) (Lo' : Lat ξ' (Module.Dual Ω' V')) (T : Set (Cpt ξ)) (T' : Set (Cpt ξ')) (r : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsCptGen ξ' → IsExtOver i j → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (Lo.map W.dualRestrict).IsVBOn T r ⊤ → (∀ p' ∈ T', ∃ hq : genPt ξ ⤳ f p'.1, (⟨f p'.1, hq⟩ : Cpt ξ) ∈ T ∧ (0 < r → Lo' p' = Submodule.span (regAt ξ' p') (jd '' (Lo ⟨f p'.1, hq⟩ : Set (Module.Dual Ω V))))) → (Lo'.map W'.dualRestrict).IsVBOn T' r ⊤ := by
  intro X X' Ω Ω' _ _ ξ ξ' f i V V' _ _ _ _ j jd W W' Lo Lo' T T' r hd _ hj hjd hW hvb hT
  have hmem : ∀ e : W, j e ∈ W' := fun e => by
    rw [hW]
    exact Submodule.subset_span ⟨e, e.2, rfl⟩
  let jr : W →+ W' :=
    { toFun := fun e => ⟨j e, hmem e⟩
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun a b => Subtype.ext (map_add j _ _) }
  have hsm : ∀ (a : Ω) (e : W), jr (a • e) = i a • jr e := fun a e => Subtype.ext (hj.1 a e)
  have hext : IsExtOver i jr := ⟨hsm, fun n b hb => by
    have h1 := hj.2 n (fun k => (b k : V)) (hb.map' W.subtype W.ker_subtype)
    exact LinearIndependent.of_comp W'.subtype h1⟩
  have hs : Submodule.span Ω' (Set.range jr) = ⊤ := by
    have h1 : (Submodule.span Ω' (Set.range jr)).map W'.subtype = W' := by
      rw [Submodule.map_span]
      conv_rhs => rw [hW]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
        exact ⟨e, e.2, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact ⟨_, ⟨⟨e, he⟩, rfl⟩, rfl⟩
    have h2 := Submodule.comap_map_eq_of_injective W'.injective_subtype (Submodule.span Ω' (Set.range jr))
    rw [h1, Submodule.comap_subtype_self] at h2
    exact h2.symm
  obtain ⟨jW, hjW⟩ := DualExt.dual_ext Ω Ω' i W W' jr hext hs
  have hcomp : ∀ w, W'.dualRestrict (jd w) = jW (W.dualRestrict w) := by
    intro w
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨e, rfl⟩
    rw [hjW]
    exact hjd w e
  have hsemi : ∀ (a : Ω) (u : Module.Dual Ω W), jW (a • u) = i a • jW u := by
    intro a u
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨e, rfl⟩
    simp [hjW]
  intro p' hp'
  obtain ⟨hq, hpT, -⟩ := hT p' hp'
  obtain ⟨U, hU, b, hb, hfr⟩ := hvb _ hpT
  obtain ⟨hli', hspan'⟩ := dual_frame_ext i jr hsm hs jW hjW b (hfr _ hpT hU).1 hb
  refine ⟨f ⁻¹ᵁ U, hU, fun k => jW (b k), hspan', fun q' hq' hq'U => ⟨hli', ?_⟩⟩
  obtain ⟨hq2, hqT, hL⟩ := hT q' hq'
  have hfrq := (hfr _ hqT hq'U).2
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : Subsingleton (Module.Dual Ω' W') := by
      rw [← Submodule.subsingleton_iff Ω', ← subsingleton_iff_bot_eq_top]
      rw [← hspan']
      simp
    exact Subsingleton.elim _ _
  · obtain ⟨hq3, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q'
    apply le_antisymm
    · show Submodule.map _ _ ≤ _
      rw [hL hr, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      show W'.dualRestrict (jd w) ∈ _
      rw [hcomp]
      have hin : W.dualRestrict w ∈ Submodule.span (regAt ξ ⟨f q'.1, hq2⟩) (Set.range b) := by
        rw [← hfrq]
        exact ⟨w, hw, rfl⟩
      have key : ∀ y ∈ Submodule.span (regAt ξ ⟨f q'.1, hq2⟩) (Set.range b),
          jW y ∈ Submodule.span (regAt ξ' q') (Set.range fun k => jW (b k)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          exact Submodule.subset_span ⟨k, rfl⟩
        | zero => simp
        | add y z _ _ hy hz =>
          rw [map_add]
          exact Submodule.add_mem _ hy hz
        | smul a y _ hy =>
          have : jW (a • y) = (⟨i a, hreg _ a.2⟩ : regAt ξ' q') • jW y := hsemi (a : Ω) y
          rw [this]
          exact Submodule.smul_mem _ _ hy
      exact key _ hin
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hin : b k ∈ (Lo.map W.dualRestrict) ⟨f q'.1, hq2⟩ := by
        rw [hfrq]
        exact Submodule.subset_span ⟨k, rfl⟩
      obtain ⟨w, hw, hwk⟩ := hin
      refine ⟨jd w, ?_, ?_⟩
      · rw [hL hr]
        exact Submodule.subset_span ⟨w, hw, rfl⟩
      · show W'.dualRestrict (jd w) = jW (b k)
        rw [hcomp]
        exact congrArg jW hwk

end GlobalTheory.CompanionTheory.Ar.VbPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagVectorBundle
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.FlagVB

theorem exists_gen_of_summand {A E : Type} [CommRing A] [IsLocalRing A] [AddCommGroup E] [Module A E]
    {M M' Q : Submodule A E} (hMM : M ≤ M') (hM' : M' ≤ Q ⊔ M) (hd : Disjoint Q M) {m m' : ℕ} (hm : m' = m + 1)
    (bM : Module.Basis (Fin m) A M) (bM' : Module.Basis (Fin m') A M') :
    ∃ e ∈ M', M' = M ⊔ Submodule.span A {e} := by
  classical
  set P : Submodule A E := Q ⊓ M' with hP
  have hPM' : P ≤ M' := inf_le_right
  have hsup : P ⊔ M = M' := by
    apply le_antisymm (sup_le hPM' hMM)
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hM' hx)
    have hyM' : y ∈ M' := by
      have := M'.sub_mem hx (hMM hz)
      simpa using this
    exact Submodule.mem_sup.2 ⟨y, ⟨hy, hyM'⟩, z, hz, rfl⟩
  have hdP : Disjoint P M := hd.mono_left inf_le_left
  let f : (P × M) →ₗ[A] M' := LinearMap.coprod (Submodule.inclusion hPM') (Submodule.inclusion hMM)
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ h
    have h' : (x : E) + (y : E) = 0 := by
      have := congrArg Subtype.val h
      simpa [f] using this
    have hx : (x : E) = -(y : E) := eq_neg_of_add_eq_zero_left h'
    have hxM : (x : E) ∈ M := hx ▸ M.neg_mem y.2
    have hx0 : (x : E) = 0 := (Submodule.disjoint_def.1 hdP) _ x.2 hxM
    have hy0 : (y : E) = 0 := by simpa [hx0] using h'
    ext <;> simp [hx0, hy0]
  have hfsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rw [← hsup] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), by ext; simp [f]⟩
  let g : (P × M) ≃ₗ[A] M' := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  haveI : Module.Free A M' := Module.Free.of_basis bM'
  haveI : Module.Finite A M' := Module.Finite.of_basis bM'
  haveI : Module.Free A M := Module.Free.of_basis bM
  haveI : Module.Finite A M := Module.Finite.of_basis bM
  haveI : Module.Free A (P × M) := Module.Free.of_equiv g.symm
  haveI : Module.Finite A (P × M) := Module.Finite.equiv g.symm
  haveI : Module.Finite A P := Module.Finite.of_surjective (LinearMap.fst A P M) LinearMap.fst_surjective
  haveI : Module.Projective A P :=
    Module.Projective.of_split (LinearMap.inl A P M) (LinearMap.fst A P M) (by ext; simp)
  haveI : Module.Free A P := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank A P = 1 := by
    have h1 := g.finrank_eq
    rw [Module.finrank_prod, Module.finrank_eq_card_basis bM, Module.finrank_eq_card_basis bM'] at h1
    simp only [Fintype.card_fin] at h1
    omega
  let c : Module.Basis Unit A P := Module.basisUnique Unit hr
  refine ⟨(c ()).1, hPM' (c ()).2, ?_⟩
  have hPs : P = Submodule.span A {((c ()).1 : E)} := by
    have h := c.span_eq
    have h2 := congrArg (Submodule.map P.subtype) h
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h2
    refine h2.symm.trans ?_
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_range, Set.mem_singleton_iff, Submodule.subtype_apply, exists_exists_eq_and]
    exact ⟨fun ⟨a, h⟩ => h ▸ rfl, fun h => ⟨(), h.symm⟩⟩
  rw [← hPs, sup_comm, hsup]

theorem exists_basis_of_frame {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (A : Subring Ω) {m : ℕ}
    {b : Fin m → E} (hb : LinearIndependent Ω b) {M : Submodule A E} (hM : M = Submodule.span A (Set.range b)) :
    Nonempty (Module.Basis (Fin m) A M) := by
  subst hM
  have h : LinearIndependent A b := hb.restrict_scalars (by
    intro x y h
    have := congrArg (fun t : Ω => t) h
    simpa [Subring.smul_def] using this)
  exact ⟨Module.Basis.span h |>.map (LinearEquiv.refl _ _)⟩

section Flag

variable {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ}

theorem flagStep_mono (b : Fin r → E) {i j : ℕ} (h : i ≤ j) : flagStep Ω b i ≤ flagStep Ω b j :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

theorem flagStep_min (b : Fin r → E) (i : ℕ) : flagStep Ω b i = flagStep Ω b (min i r) := by
  unfold flagStep
  congr 2
  ext k
  simp [k.2]

theorem flagStep_last (b : Fin r → E) : flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold flagStep
  congr 1
  ext x
  simp

theorem finrank_flagStep {b : Fin r → E} (hb : LinearIndependent Ω b) {n : ℕ} (hn : n ≤ r) :
    Module.finrank Ω (flagStep Ω b n) = n := by
  have h : flagStep Ω b n = Submodule.span Ω (Set.range (b ∘ Fin.castLE hn)) := by
    unfold flagStep
    congr 1
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨Fin.castLE hn k, k.2, rfl⟩
  rw [h, finrank_span_eq_card (hb.comp _ (Fin.castLE_injective hn))]
  simp

theorem exists_adapted (A : Subring Ω) [IsLocalRing A] (N : Submodule A E) (b₀ : Fin r → E)
    (hfr : ∀ n ≤ r, ∃ m, m = n ∧ ∃ d : Fin m → E, LinearIndependent Ω d ∧
      Submodule.span Ω (Set.range d) = flagStep Ω b₀ n ∧
      N ⊓ (flagStep Ω b₀ n).restrictScalars A = Submodule.span A (Set.range d))
    (hQ : ∀ n, ∃ Q : Submodule A E, Disjoint Q (N ⊓ (flagStep Ω b₀ n).restrictScalars A) ∧
      Q ⊔ (N ⊓ (flagStep Ω b₀ n).restrictScalars A) = N) :
    ∃ c : ℕ → E, (∀ i ≤ r, Submodule.span Ω (c '' Set.Iio i) = flagStep Ω b₀ i) ∧
      N ⊓ (flagStep Ω b₀ r).restrictScalars A = Submodule.span A (c '' Set.Iio r) := by
  classical
  have key : ∀ n, n ≤ r → ∃ c : ℕ → E, (∀ i ≤ n, Submodule.span Ω (c '' Set.Iio i) = flagStep Ω b₀ i) ∧
      N ⊓ (flagStep Ω b₀ n).restrictScalars A = Submodule.span A (c '' Set.Iio n) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : flagStep Ω b₀ 0 = ⊥ := by simp [flagStep]
      refine ⟨fun _ => 0, fun i hi => ?_, ?_⟩
      · obtain rfl : i = 0 := by omega
        simp [h0]
      · simp [h0]
    | succ n ih =>
      intro hn
      obtain ⟨c, h1, h2⟩ := ih (by omega)
      obtain ⟨m, hm, d, hd, -, hdA⟩ := hfr n (by omega)
      obtain ⟨m', hm', d', hd', hdΩ', hdA'⟩ := hfr (n + 1) hn
      obtain ⟨Q, hQ1, hQ2⟩ := hQ n
      obtain ⟨bM⟩ := exists_basis_of_frame A hd hdA
      obtain ⟨bM'⟩ := exists_basis_of_frame A hd' hdA'
      have hle : flagStep Ω b₀ n ≤ flagStep Ω b₀ (n + 1) := flagStep_mono b₀ (Nat.le_succ n)
      have hMM : N ⊓ (flagStep Ω b₀ n).restrictScalars A ≤ N ⊓ (flagStep Ω b₀ (n + 1)).restrictScalars A :=
        inf_le_inf_left _ (fun x hx => hle hx)
      have hM' : N ⊓ (flagStep Ω b₀ (n + 1)).restrictScalars A ≤
          Q ⊔ (N ⊓ (flagStep Ω b₀ n).restrictScalars A) := by
        rw [hQ2]
        exact inf_le_left
      obtain ⟨e, he, hgen⟩ := exists_gen_of_summand hMM hM' hQ1 (by omega) bM bM'
      have himg : ∀ i ≤ n, Function.update c n e '' Set.Iio i = c '' Set.Iio i := fun i hi =>
        Set.image_congr fun k hk => Function.update_of_ne (by
          have : k < i := hk
          omega) _ _
      have himg' : Function.update c n e '' Set.Iio (n + 1) = insert e (c '' Set.Iio n) := by
        have : Set.Iio (n + 1) = insert n (Set.Iio n) := by
          ext k
          simp only [Set.mem_Iio, Set.mem_insert_iff]
          omega
        rw [this, Set.image_insert_eq, Function.update_self, himg n le_rfl]
      refine ⟨Function.update c n e, fun i hi => ?_, ?_⟩
      · rcases Nat.lt_or_ge i (n + 1) with hlt | hge
        · rw [himg i (by omega), h1 i (by omega)]
        · obtain rfl : i = n + 1 := by omega
          rw [himg', Submodule.span_insert, h1 n le_rfl]
          apply le_antisymm
          · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 he.2) hle
          · rw [← hdΩ', Submodule.span_le]
            rintro _ ⟨k, rfl⟩
            have hk : d' k ∈ N ⊓ (flagStep Ω b₀ (n + 1)).restrictScalars A := by
              rw [hdA']
              exact Submodule.subset_span ⟨k, rfl⟩
            rw [hgen] at hk
            obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hk
            obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
            rw [← hyz]
            refine add_mem (Submodule.mem_sup_right hy.2) (Submodule.mem_sup_left ?_)
            exact Submodule.smul_mem _ (a : Ω) (Submodule.mem_span_singleton_self e)
      · rw [himg', Submodule.span_insert, ← h2, hgen, sup_comm]
  obtain ⟨c, h1, h2⟩ := key r le_rfl
  exact ⟨c, h1, h2⟩

end Flag

end GlobalTheory.CompanionTheory.Ar.FlagVB

namespace GlobalTheory.CompanionTheory.Ar

theorem isFlagVBOn_inter_of_steps : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (g r : ℕ) (W : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ → (∀ k, b₀ k ∈ W) → L.IsVBOn T g W → (∀ n : ℕ, ∃ s W', (L.map (flagStep Ω b₀ n).mkQ).IsVBOn T s W') → (L.inter (Submodule.span Ω (Set.range b₀))).IsFlagVBOn T b₀ := by
  intro X Ω _ ξ E _ _ L T g r W b₀ hli hW hL hq p hp
  classical
  haveI : IsLocalRing (regAt ξ p) := (GlobalTheory.T.regAt_local_order_fraction X Ω ξ).1 p
  have hFW : ∀ n, flagStep Ω b₀ n ≤ W := fun n =>
    Submodule.span_le.2 (by
      rintro _ ⟨k, -, rfl⟩
      exact hW k)
  have hv : ∀ n, (L.inter (flagStep Ω b₀ n)).IsVBOn T (Module.finrank Ω (flagStep Ω b₀ n)) (flagStep Ω b₀ n) ∧
      ∀ p ∈ T, ∃ Q : Submodule (regAt ξ p) E, Disjoint Q (L.inter (flagStep Ω b₀ n) p) ∧
        Q ⊔ L.inter (flagStep Ω b₀ n) p = L p := fun n => by
    obtain ⟨s, W', h⟩ := hq n
    exact GlobalTheory.T.lattice_sub_quotient_split X Ω ξ E L T g s W (flagStep Ω b₀ n) W' (hFW n) hL h
  obtain ⟨c, h1, h2⟩ := FlagVB.exists_adapted (regAt ξ p) (L p) b₀ (fun n hn => by
      obtain ⟨U, hU, d, hd, hfr⟩ := (hv n).1 p hp
      obtain ⟨hd1, hd2⟩ := hfr p hp hU
      exact ⟨_, FlagVB.finrank_flagStep hli hn, d, hd1, hd, hd2⟩)
    (fun n => (hv n).2 p hp)
  let b : Fin r → E := fun k => c k
  have himg : ∀ i, b '' {k | (k : ℕ) < i} = c '' Set.Iio (min i r) := fun i => by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, lt_min hk k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have hk' := lt_min_iff.1 (show k < min i r from hk)
      exact ⟨⟨k, hk'.2⟩, hk'.1, rfl⟩
  have hflag : ∀ i, flagStep Ω b i = flagStep Ω b₀ i := fun i => by
    rw [FlagVB.flagStep_min b₀ i, ← h1 (min i r) (min_le_right _ _), ← himg i]
    rfl
  have hrange : Set.range b = c '' Set.Iio r := by
    have := himg r
    rw [min_self] at this
    rw [← this]
    ext x
    simp
  have hspan : Submodule.span Ω (Set.range b) = flagStep Ω b₀ r := by
    rw [hrange, h1 r le_rfl]
  have hlib : LinearIndependent Ω b := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan, FlagVB.finrank_flagStep hli le_rfl]
    simp
  have hV : Submodule.span Ω (Set.range b₀) = flagStep Ω b₀ r := (FlagVB.flagStep_last b₀).symm
  have hframe : (L.inter (Submodule.span Ω (Set.range b₀))).IsFrameAt b p := by
    refine ⟨hlib, ?_⟩
    rw [hV, hrange]
    exact h2
  have hcoh : (L.inter (Submodule.span Ω (Set.range b₀))).IsCohOn T := by
    have hvb := (hv r).1
    rw [← hV] at hvb
    exact (GlobalTheory.T.coherent_lattice_closure X Ω ξ E E (L.inter (Submodule.span Ω (Set.range b₀))) (L.inter (Submodule.span Ω (Set.range b₀))) T).1 _ _ hvb
  obtain ⟨U, hU, hall⟩ := GlobalTheory.T.frame_open_neighbourhood X Ω ξ E _ T r b p hcoh hp hframe
  exact ⟨U, hU, b, hflag, hall⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineLatticeGenericSections
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_regAt_genPt_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (a : Ω) :
    a ∈ regAt ξ ⟨genPt ξ, specializes_refl _⟩ := by
  obtain ⟨g, hg⟩ := h.bij.2 a
  refine ⟨g, ?_⟩
  rw [← hg]
  simp only [genMap, genPt, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  rfl

theorem genPt_mem_genFibre_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (O : Type) [CommRing O] [Algebra O Ω]
    (hi : Function.Injective (algebraMap O Ω)) :
    (⟨genPt ξ, specializes_refl _⟩ : Cpt ξ) ∈ genFibre O ξ := fun o ho =>
  ⟨fun h0 => ho (hi (by rw [h0, map_zero])), mem_regAt_genPt_of_isCptGen h _,
    mem_regAt_genPt_of_isCptGen h _⟩

theorem mem_lat_genFibre_iff_const_mul : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ConstClosed O Ω → ∀ (L : Lat ξ Ω) (t : Ω), (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∀ u : Ω, (∀ p ∈ genFibre O ξ, u ∈ L p) ↔ ∃ x y : O, y ≠ 0 ∧ u * algebraMap O Ω y = algebraMap O Ω x * t := by
  intro X Ω _ ξ O _ _ _ s _ hs hi hξ hc L t ht u
  have ht0 : t ≠ 0 := (ht _ (genPt_mem_genFibre_of_isCptGen hξ O hi)).1
  constructor
  · intro hu
    have hreg : ∀ p ∈ genFibre O ξ, u / t ∈ regAt ξ p := by
      intro p hp
      have h1 := hu p hp
      rw [(ht p hp).2] at h1
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
      replace hc : (c : Ω) * t = u := hc
      rw [← hc, mul_div_cancel_right₀ _ ht0]
      exact c.2
    obtain ⟨x, y, hy, e⟩ := hc _ ((GlobalTheory.T.regular_everywhere_isIntegral X Ω ξ O s hs hi hξ (u / t)).2 hreg)
    refine ⟨x, y, hy, ?_⟩
    rw [← e]
    field_simp
  · rintro ⟨x, y, hy, e⟩ p hp
    rw [(ht p hp).2]
    have hx : algebraMap O Ω x ∈ regAt ξ p := by
      by_cases h0 : x = 0
      · rw [h0, map_zero]; exact zero_mem _
      · exact (hp x h0).2.1
    have hyu := hp y hy
    refine Submodule.mem_span_singleton.2 ⟨⟨_, mul_mem hx hyu.2.2⟩, ?_⟩
    change algebraMap O Ω x * (algebraMap O Ω y)⁻¹ * t = u
    have := hyu.1
    rw [mul_right_comm, ← e]
    field_simp

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldIntegersInIntegrallyClosed
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.IntEmb

theorem ringOfIntegers_embedding_mem_range
    (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω]
    [IsIntegrallyClosed A] (E : Type) [Field E] [NumberField E] (σ : E →+* Ω) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A Ω).range := by
  have hℤ : IsIntegral ℤ (σ (a : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom ℤ) σ (RingHom.ext_int _ _)
      (NumberField.RingOfIntegers.isIntegral_coe a)
  have hA : IsIntegral A (σ (a : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom A) (RingHom.id Ω) (RingHom.ext_int _ _) hℤ
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp hA
  exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.Ar.IntEmb
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropZProvedStatement
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.PropZ_proved : GlobalTheory.CompanionTheory.Ar.Flat.PropZ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds | exact GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds <;> assumption)
end

