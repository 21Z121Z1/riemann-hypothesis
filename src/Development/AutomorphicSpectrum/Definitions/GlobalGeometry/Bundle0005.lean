import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

def LieModel.IsHTFormOver (M : LieModel G ξ E) (N : ℕ) {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ X)
    (k : R →+* Ω) (w : Module.Dual Ω E) : Prop :=
  ∃ (_ : IsDomain R) (T : Type) (_ : CommGroup T) (Γ : BT.QFGroup R T)
    (i : Γ.G.left ⟶ G.left) (L : Type) (_ : AddCommGroup L) (_ : Module R L)
    (M₀ : LieModel G x L) (j : L → E) (χ : T →* Rˣ) (w₀ : Module.Dual R L),
    Γ.IsTorsionAlong G x N i ∧ (∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left) ∧
      Γ.IsHT i M₀ N χ w₀ ∧ ∀ e, w (j e) = k (w₀ e)

def LieModel.IsHTFormAt (M : LieModel G ξ E) (N : ℕ) (p : Cpt ξ) (w : Module.Dual Ω E) : Prop :=
  M.IsHTFormOver N (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) (genMap ξ p) w

def LieModel.htLat (M : LieModel G ξ E) (N : ℕ) : Lat ξ (Module.Dual Ω E) := fun p =>
  Submodule.span (regAt ξ p) {w | M.IsHTFormAt N p w}

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def genFibre (O : Type) [CommRing O] [Algebra O Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Set (Cpt ξ) :=
  {p | ∀ o : O, o ≠ 0 → unitAt ξ p (algebraMap O Ω o)}

def ConstClosed (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] : Prop :=
  ∀ a : Ω, IsAlgebraic O a → ∃ x y : O, y ≠ 0 ∧ a * algebraMap O Ω y = algebraMap O Ω x

def lineLat (A B : Lat ξ E) (p q : ℕ) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) : Lat ξ Ω := fun x =>
  Submodule.span (regAt ξ x) {t | ∃ f : Ω, IsCoeffAt A B p q a b x f ∧ t = f⁻¹}

def SplitModAt (A : Lat ξ E) (ϖ : Ω) {N : ℕ} (J : Cpt ξ → (E →ₗ[Ω] (Fin N → Ω))) (x y : Cpt ξ) : Prop :=
  (∀ w ∈ A y, ∀ k, J x w k ∈ regAt ξ y ∧ (J x w k - J y w k) / ϖ ∈ regAt ξ y) ∧
    ∃ R : (Fin N → Ω) →ₗ[Ω] E, (∀ k, R (Pi.single k 1) ∈ A y) ∧ ∀ w ∈ A y, ∃ w' ∈ A y, R (J x w) = w + ϖ • w'

def ExactModLat (A B : Lat ξ E) (ϖ : Ω) (N : ℕ) : Prop :=
  ∃ J J' : Cpt ξ → (E →ₗ[Ω] (Fin N → Ω)), ∀ x : Cpt ξ, ¬ unitAt ξ x ϖ → ∃ U : X.Opens, x.1 ∈ U ∧
    ∀ y : Cpt ξ, y.1 ∈ U → ¬ unitAt ξ y ϖ → SplitModAt A ϖ J x y ∧ SplitModAt B ϖ J' x y ∧
      ∀ w ∈ A y, ∀ w' ∈ B y, dotProduct (J x w) (J' x w') / ϖ ∈ regAt ξ y

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LocalComponentsSurjective
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Crv

open AlgebraicGeometry CategoryTheory

variable {K : Type} [Field K] {X : Scheme.{0}}

structure CurveIn (C : ACurve K) (ζ : Spec (CommRingCat.of K) ⟶ X) where

  x : ∀ i : C.I, Spec (CommRingCat.of (C.v i).valuationSubring) ⟶ X
  gen : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ x i = ζ
  ae : ∀ U : X.Opens, centre ζ ∈ U → {i | centre (x i) ∉ U}.Finite

variable {C : ACurve K} {ζ : Spec (CommRingCat.of K) ⟶ X}

def CurveIn.lieLat (Y : CurveIn C ζ) {G : Over X} [GrpObj G] {V : Type} [AddCommGroup V] [Module K V]
    (M : LieModel G ζ V) : C.I → AddSubgroup V := fun i =>
  AddSubgroup.closure {e | ∃ v : epsAt (Y.x i) ⟶ G, IsTanAt G (Y.x i) v ∧
    (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap (C.v i).valuationSubring.subtype)) ≫ v.left}

def CurveIn.IsDeg (Y : CurveIn C ζ) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (Λ : Lat ξ Ω)
    (n : ℤ) : Prop :=
  ∃ (h₀ : genPt ξ ⤳ centre ζ) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (s₀ : Ω) (s : C.I → Ω) (r : C.I → K),
    Λ.IsGenAt ⟨centre ζ, h₀⟩ s₀ ∧ (∀ i, Λ.IsGenAt ⟨centre (Y.x i), h i⟩ (s i)) ∧
      (∀ i, r i ≠ 0 ∧ ValAt ξ ζ (s i / s₀) (r i)) ∧ {i | C.v i (r i) ≠ 1}.Finite ∧
      n = ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (r i))

def coordDeg (C : ACurve K) {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)] (w : (Σ k, ι k) → K)
    (a : B → ℤ) : ℤ :=
  ∑ k, a k * ∑ᶠ i, (C.w i : ℤ) * WithZero.log (Finset.univ.sup fun c : ι k => C.v i (w ⟨k, c⟩))

def lmuExp {T : Type} (j q : ℕ) (μ : T → ℕ → ℤ) : (Σ s : T ⊕ T, Fin (Sum.elim (fun _ => j) (fun _ => q) s)) → ℤ
  | ⟨Sum.inl τ, i⟩ => -μ τ (i.1 + 1)
  | ⟨Sum.inr τ, i⟩ => μ τ (j + q - i.1)

end GlobalTheory.CompanionTheory.Ar.Crv
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NotIsGenericFlagSelf
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagModel

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem isFlagVBOn_frame {r : ℕ} (b : Fin r → E) (hb : LinearIndependent Ω b) (T : Set (Cpt ξ)) :
    Lat.IsFlagVBOn (fun p => Submodule.span (regAt ξ p) (Set.range b) : Lat ξ E) T b := by
  intro p _
  exact ⟨⊤, trivial, b, fun _ => rfl, fun q _ _ => And.intro hb rfl⟩

theorem not_mem_flagStep {r : ℕ} (b : Fin r → E) (hb : LinearIndependent Ω b) (i : Fin r) :
    b i ∉ flagStep Ω b i := by
  exact hb.notMem_span_image (by simp)

theorem gr_isGenAt {r : ℕ} (L : Lat ξ E) (b b₀ : Fin r → E) (p : Cpt ξ) (hL : L.IsFrameAt b p)
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) (c : Ω)
    (hc : b i - c • b₀ i ∈ flagStep Ω b₀ i) : (L.gr b₀ i).IsGenAt p c := by
  obtain ⟨hb, hLp⟩ := hL
  have hbi : b i ∉ flagStep Ω b i := not_mem_flagStep b hb i
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hbi
    rw [hF]
    simpa using hc
  refine ⟨hc0, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro t ⟨e, he, het⟩
    rw [hLp] at he
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (regAt ξ p)).mp he
    have het' : ∑ k, (d k : Ω) • b k - t • b₀ i ∈ flagStep Ω b₀ i := het
    set S : Submodule Ω E := Submodule.span Ω (b '' {k | k ≠ i}) with hS
    have hFS : flagStep Ω b₀ i ≤ S := by
      rw [← hF]
      refine Submodule.span_mono ?_
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨k, fun hki => ?_, rfl⟩
      subst hki
      exact lt_irrefl (k : ℕ) hk
    have h1 : c • (∑ k, (d k : Ω) • b k - t • b₀ i) ∈ S := S.smul_mem c (hFS het')
    have h2 : c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k ∈ S :=
      S.smul_mem c (Submodule.sum_mem _ fun k hk =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, Finset.ne_of_mem_erase hk, rfl⟩))
    have h3 : t • (b i - c • b₀ i) ∈ S := S.smul_mem t (hFS hc)
    have heq : (c * (d i : Ω) - t) • b i =
        c • (∑ k, (d k : Ω) • b k - t • b₀ i) - c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k -
          t • (b i - c • b₀ i) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      module
    have key : (c * (d i : Ω) - t) • b i ∈ S := by
      rw [heq]
      exact S.sub_mem (S.sub_mem h1 h2) h3
    have hzero : c * (d i : Ω) - t = 0 := by
      by_contra hne
      apply hb.notMem_span_image (s := {k | k ≠ i}) (x := i) (by simp)
      have := S.smul_mem (c * (d i : Ω) - t)⁻¹ key
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    refine Submodule.mem_span_singleton.mpr ⟨d i, ?_⟩
    show (d i : Ω) * c = t
    rw [mul_comm]
    exact sub_eq_zero.mp hzero
  · refine Submodule.span_le.mpr ?_
    rintro _ rfl
    refine Submodule.subset_span ⟨b i, ?_, hc⟩
    rw [hLp]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem exists_gen {r : ℕ} (L : Lat ξ E) (T : Set (Cpt ξ)) (b₀ : Fin r → E) (h : L.IsFlagVBOn T b₀)
    (p : Cpt ξ) (hp : p ∈ T) (i : Fin r) : ∃ c, (L.gr b₀ i).IsGenAt p c := by
  obtain ⟨U, hpU, b, hF, hfr⟩ := h p hp
  have hL := hfr p hp hpU
  have hmem : b i ∈ flagStep Ω b₀ ((i : ℕ) + 1) := by
    rw [← hF]
    exact Submodule.subset_span ⟨i, Nat.lt_add_one _, rfl⟩
  have hsub : b₀ '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1} ⊆
      insert (b₀ i) (b₀ '' {k : Fin r | (k : ℕ) < i}) := by
    rintro _ ⟨k, hk, rfl⟩
    rcases (Nat.lt_add_one_iff.mp hk).lt_or_eq with h' | h'
    · exact Set.mem_insert_of_mem _ ⟨k, h', rfl⟩
    · rw [Fin.ext h']
      exact Set.mem_insert _ _
  have hmem' : b i ∈ Submodule.span Ω (insert (b₀ i) (b₀ '' {k : Fin r | (k : ℕ) < i})) :=
    Submodule.span_mono hsub hmem
  rw [Submodule.span_insert] at hmem'
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem'
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  refine ⟨a, gr_isGenAt L b b₀ p hL hF i a ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz

theorem zpow_ratio (Λ : Lat ξ Ω) (p : Cpt ξ) (s t : Ω) (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) (n : ℤ) :
    (t / s) ^ n ∈ regAt ξ p := by
  obtain ⟨hs0, hsp⟩ := hs
  obtain ⟨ht0, htp⟩ := ht
  have h1 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hsp, htp]
    exact Submodule.mem_span_singleton_self t
  have h2 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← htp, hsp]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.mp h2
  have hts : t / s = a := by
    rw [div_eq_iff hs0]
    exact ha.symm
  have hst : s / t = a' := by
    rw [div_eq_iff ht0]
    exact ha'.symm
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, hts]
    exact pow_mem a.2 m
  · rw [zpow_negSucc, ← inv_pow, inv_div, hst]
    exact pow_mem a'.2 _

theorem tens_isGenAt {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs i).1, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro t ⟨s', hs', rfl⟩
    have hr : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_ratio (Λ i) p (s i) (s' i) (hs i) (hs' i) (a i)
    refine Submodule.mem_span_singleton.mpr ⟨⟨_, hr⟩, ?_⟩
    show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]
  · exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨s, hs, rfl⟩)

theorem grTens_exists_gen {S : Type} [Fintype S] {r : S → ℕ} (L : S → Lat ξ E) (b₀ : ∀ σ, Fin (r σ) → E)
    (a : (Σ σ, Fin (r σ)) → ℤ) (T : Set (Cpt ξ)) (h : ∀ σ, (L σ).IsFlagVBOn T (b₀ σ)) (p : Cpt ξ) (hp : p ∈ T) :
    ∃ c, (Lat.grTens L b₀ a).IsGenAt p c := by
  have hq : ∀ q : Σ σ, Fin (r σ), ∃ c, ((L q.1).gr (b₀ q.1) q.2).IsGenAt p c :=
    fun q => exists_gen (L q.1) T (b₀ q.1) (h q.1) p hp q.2
  choose s hs using hq
  exact ⟨_, tens_isGenAt _ a p s hs⟩

def jPlane (Ω : Type) [Field Ω] : (Fin 2 → Ω) →+ (Fin 2 → RatFunc Ω) :=
  ((algebraMap Ω (RatFunc Ω)).toAddMonoidHom).compLeft (Fin 2)

theorem isGenericFlag_plane :
    IsGenericFlag (Ω := Ω) (Ω' := RatFunc Ω) (jPlane Ω) (S := Unit) (r := fun _ => 2) (fun _ => ⊤)
      (fun _ => ![![1, RatFunc.X], ![0, 1]]) 1 := by
  have hj : ∀ (v : Fin 2 → Ω) (m : Fin 2), jPlane Ω v m = algebraMap Ω (RatFunc Ω) (v m) :=
    fun _ _ => rfl
  have hU : ∀ (ι : Type) (hι : Unique ι) (x : ι → RatFunc Ω), x default = RatFunc.X →
      AlgebraicIndependent Ω x := by
    intro ι hι x hx
    rw [algebraicIndependent_unique_type_iff, hx]
    exact RatFunc.transcendental_X
  have key : ∀ K : IntermediateField Ω (RatFunc Ω), RatFunc.X ∈ K →
      Module.finrank K (RatFunc Ω) = 1 := by
    intro K hK
    have hK' : K = ⊤ := by
      rw [eq_top_iff, ← RatFunc.adjoin_X]
      exact IntermediateField.adjoin_simple_le_iff.mpr hK
    subst hK'
    exact IntermediateField.finrank_top
  refine ⟨fun _ => ⇑(Pi.basisFun Ω (Fin 2)), fun _ => !![1, 0; RatFunc.X, 1],
    fun _ => ⟨(Pi.basisFun Ω (Fin 2)).linearIndependent, (Pi.basisFun Ω (Fin 2)).span_eq⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.one_pos, ?_⟩
  · intro a e
    ext m
    simp [hj, map_mul]
  · intro _
    convert (Pi.basisFun (RatFunc Ω) (Fin 2)).linearIndependent using 1
    all_goals first
      | rfl
      | (ext k m
         fin_cases k <;> fin_cases m <;> simp [hj])
  · intro _
    refine LinearIndependent.pair_iff.mpr fun s t h => ?_
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    subst h0
    simpa using h1
  · intro _ k
    fin_cases k <;> simp
  · intro _ l k h
    fin_cases l <;> fin_cases k <;> simp at h ⊢
  · intro _ i
    congr 1
    ext k m
    fin_cases k <;> fin_cases m <;> simp [hj, Fin.sum_univ_two, Finset.sum_apply]
  · refine hU _ ?_ _ ?_
    · refine ⟨⟨⟨(), ⟨(1, 0), by decide⟩⟩⟩, ?_⟩
      rintro ⟨⟨⟩, ⟨⟨l, k⟩, h⟩⟩
      fin_cases l <;> fin_cases k <;> first | rfl | exact absurd h (by decide)
    · rfl
  · exact key _ (IntermediateField.subset_adjoin _ _ ⟨⟨(), (1, 0)⟩, by simp⟩)

theorem not_isGenericFlag_self {E' : Type} [AddCommGroup E'] [Module Ω E'] (j : E →+ E') (V : Unit → Submodule Ω E)
    (b₀ : Unit → Fin 2 → E') (d : ℕ) : ¬ IsGenericFlag (Ω' := Ω) j (r := fun _ => 2) V b₀ d := by
  rintro ⟨c, u, -, -, -, -, -, -, -, hai, -, -⟩
  exact hai.transcendental ⟨(), ⟨(1, 0), by decide⟩⟩ (isAlgebraic_algebraMap (R := Ω) (A := Ω) _)

end GlobalTheory.CompanionTheory.Ar.FlagModel
end
end

