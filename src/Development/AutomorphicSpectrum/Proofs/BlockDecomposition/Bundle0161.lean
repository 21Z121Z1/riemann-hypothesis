import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0152
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0142

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHEmptyBij
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

universe w w'

namespace GlobalTheory.CompanionTheory.Onto

variable {R : Type} [CommRing R]

abbrev prodCx {I : Type} (K : I → Cx.{w} R) : Cx.{w} R where
  X n := ∀ i, (K i).X n
  d n := LinearMap.pi fun i => ((K i).d n).comp (LinearMap.proj i)
  dd n x := funext fun i => (K i).dd n (x i)

def prodHom {I : Type} {K : I → Cx.{w} R} {L : I → Cx.{w'} R}
    (φ : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R)) : Cx.Hom (prodCx K) (prodCx L) (RingHom.id R) where
  f n := LinearMap.pi fun i => ((φ i).f n).comp (LinearMap.proj i)
  comm n x := funext fun i => (φ i).comm n (x i)

theorem mem_B_prod {I : Type} (K : I → Cx.{w} R) (n : ℕ) (a : (prodCx K).X n) :
    a ∈ (prodCx K).B n ↔ ∀ i, a i ∈ (K i).B n := by
  cases n with
  | zero =>
    constructor
    · intro h i
      have h0 : a = 0 := h
      rw [h0]
      exact Submodule.zero_mem _
    · intro h
      exact funext fun i => h i
  | succ n =>
    constructor
    · rintro ⟨b, rfl⟩ i
      exact ⟨b i, rfl⟩
    · intro h
      choose b hb using h
      exact ⟨b, funext hb⟩

theorem prod_bij {I : Type} {K : I → Cx.{w} R} {L : I → Cx.{w'} R}
    (φ : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R))
    (h : ∀ i n, Function.Bijective ((φ i).mapH n)) (n : ℕ) :
    Function.Bijective ((prodHom φ).mapH n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (prodCx K) n).1 x
    have hb : (prodCx L).d n ((prodHom φ).f n a) = 0 := by rw [(prodHom φ).comm, ha, map_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls _ n a ha hb, (CrystallineSemistableComparison.P.cls_surj _ n).2.1 _ hb, mem_B_prod] at hx
    rw [(CrystallineSemistableComparison.P.cls_surj _ n).2.1, mem_B_prod]
    intro i
    have hai : (K i).d n (a i) = 0 := congrFun ha i
    have hbi : (L i).d n ((φ i).f n (a i)) = 0 := by rw [(φ i).comm, hai, map_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj _ n).2.1 _ hai]
    apply (injective_iff_map_eq_zero _).1 (h i n).1
    rw [CrystallineSemistableComparison.P.mapH_cls _ n _ hai hbi, (CrystallineSemistableComparison.P.cls_surj _ n).2.1]
    exact hx i
  · intro y
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (prodCx L) n).1 y
    have hbi : ∀ i, (L i).d n (b i) = 0 := fun i => congrFun hb i
    have key : ∀ i, ∃ a, ∃ ha : (K i).d n a = 0, (φ i).f n a - b i ∈ (L i).B n := by
      intro i
      obtain ⟨x, hx⟩ := (h i n).2 ((L i).cls (b i) (hbi i))
      obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (K i) n).1 x
      have hc : (L i).d n ((φ i).f n a) = 0 := by rw [(φ i).comm, ha, map_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls _ n a ha hc] at hx
      exact ⟨a, ha, ((CrystallineSemistableComparison.P.cls_surj _ n).2.2.1 _ _ hc (hbi i)).1 hx⟩
    choose a ha hab using key
    have ha' : (prodCx K).d n a = 0 := funext ha
    have hc : (prodCx L).d n ((prodHom φ).f n a) = 0 := by rw [(prodHom φ).comm, ha', map_zero]
    refine ⟨(prodCx K).cls a ha', ?_⟩
    rw [CrystallineSemistableComparison.P.mapH_cls (prodHom φ) n a ha' hc, (CrystallineSemistableComparison.P.cls_surj _ n).2.2.1 _ _ hc hb, mem_B_prod]
    exact hab

variable {ι : Type} [DecidableEq ι]

abbrev cechCos (A : Sy.{w} R ι) : CosCx.{w} R where
  K p := prodCx fun i : Fin (p + 1) → ι => A.K (ent i)
  δ p k :=
    { f := fun q => (A.term q).cech.δ p k
      comm := fun q x => funext fun t => (A.res (ent_comp t k.succAbove)).comm q (x (t ∘ k.succAbove)) }
  rel p j i q x := (A.term q).cech.rel p j i x

def cechAug (A : Sy.{w} R ι) (hA : A.Desc) : DCx.AugRow (A.K ∅) (cechCos A).dcx where
  ε q := (A.term q).aug
  hε q x := (hA q).1 x
  comm q x := funext fun t => (A.res (Finset.empty_subset (ent t))).comm q x

theorem cechAug_row (A : Sy.{w} R ι) (hA : A.Desc) (q : ℕ) :
    ((cechCos A).dcx.row q).ResUpTo 1 ((cechAug A hA).ε q) := hA q

def cechHom {A B : Sy.{w} R ι} (m : A.Hom B) :
    DCx.Hom (cechCos A).dcx (cechCos B).dcx (RingHom.id R) where
  f p q := (prodHom fun i : Fin (p + 1) → ι => m.φ (ent i)).f q
  ch p q x := by
    rw [Cos.d_apply, Cos.d_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    refine congrArg _ (funext fun t => ?_)
    exact (m.nat (ent_comp t k.succAbove) q (x (t ∘ k.succAbove))).symm
  cv p q x := (prodHom fun i : Fin (p + 1) → ι => m.φ (ent i)).comm q x

theorem cechHom_col {A B : Sy.{w} R ι} (m : A.Hom B)
    (h : ∀ S : Finset ι, S.Nonempty → ∀ n, Function.Bijective ((m.φ S).mapH n)) (p q : ℕ) :
    Function.Bijective (((cechHom m).col p).mapH q) :=
  prod_bij (fun i : Fin (p + 1) → ι => m.φ (ent i))
    (fun i n => h _ ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ n) q

theorem upTo_one {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) : UpTo (1 : R) f ↔ Function.Bijective f := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, fun y => ?_⟩
    · simpa using h1 x hx
    · simpa using h2 y
  · intro h
    refine ⟨fun x hx => ?_, fun y => ?_⟩
    · rw [one_smul]
      exact (injective_iff_map_eq_zero f).1 h.1 x hx
    · simpa using h.2 y

theorem cls_congr {K : Cx.{w} R} {n : ℕ} {a b : K.X n} (h : a = b) (ha : K.d n a = 0) (hb : K.d n b = 0) :
    K.cls a ha = K.cls b hb := by
  subst h; rfl

theorem edge_square {A B : Sy.{w} R ι} (m : A.Hom B) (hA : A.Desc) (hB : B.Desc) (n : ℕ) (a : (A.K ∅).X n) :
    (cechHom m).tot.f n ((cechAug A hA).edge.f n a) = (cechAug B hB).edge.f n ((m.φ ∅).f n a) := by
  apply Subtype.ext
  funext p q
  by_cases h : p = 0 ∧ q = n
  · obtain ⟨rfl, rfl⟩ := h
    change (cechHom m).f 0 q ((cechCos A).dcx.sgl 0 q ((cechAug A hA).ε q a) 0 q) =
      (cechCos B).dcx.sgl 0 q ((cechAug B hB).ε q ((m.φ ∅).f q a)) 0 q
    rw [DCx.sgl_self, DCx.sgl_self]
    funext t
    exact m.nat (Finset.empty_subset (ent t)) q a
  · have h' : p ≠ 0 ∨ q ≠ n := by omega
    change (cechHom m).f p q ((cechCos A).dcx.sgl 0 n ((cechAug A hA).ε n a) p q) =
      (cechCos B).dcx.sgl 0 n ((cechAug B hB).ε n ((m.φ ∅).f n a)) p q
    rw [DCx.sgl_ne _ _ h', DCx.sgl_ne _ _ h', map_zero]

theorem mapH_empty_bij {A B : Sy.{w} R ι} (m : A.Hom B) (hA : A.Desc) (hB : B.Desc)
    (h : ∀ S : Finset ι, S.Nonempty → ∀ n, Function.Bijective ((m.φ S).mapH n)) (n : ℕ) :
    Function.Bijective ((m.φ ∅).mapH n) := by
  have eA : Function.Bijective ((cechAug A hA).edge.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_row (cechAug A hA) 1 (cechAug_row A hA) n
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have eB : Function.Bijective ((cechAug B hB).edge.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_row (cechAug B hB) 1 (cechAug_row B hB) n
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have eT : Function.Bijective ((cechHom m).tot.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_map_col (cechHom m) 1 n fun p q _ => (upTo_one _).2 (cechHom_col m h p q)
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have sq : ∀ x, (cechAug B hB).edge.mapH n ((m.φ ∅).mapH n x) =
      (cechHom m).tot.mapH n ((cechAug A hA).edge.mapH n x) := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (A.K ∅) n).1 x
    have c1 : (B.K ∅).d n ((m.φ ∅).f n a) = 0 := by rw [(m.φ ∅).comm, ha, map_zero]
    have c2 : (cechCos B).dcx.tot.d n ((cechAug B hB).edge.f n ((m.φ ∅).f n a)) = 0 := by
      rw [(cechAug B hB).edge.comm, c1, map_zero]
    have c3 : (cechCos A).dcx.tot.d n ((cechAug A hA).edge.f n a) = 0 := by
      rw [(cechAug A hA).edge.comm, ha, map_zero]
    have c4 : (cechCos B).dcx.tot.d n ((cechHom m).tot.f n ((cechAug A hA).edge.f n a)) = 0 := by
      rw [(cechHom m).tot.comm, c3, map_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls (m.φ ∅) n a ha c1, CrystallineSemistableComparison.P.mapH_cls (cechAug B hB).edge n _ c1 c2,
      CrystallineSemistableComparison.P.mapH_cls (cechAug A hA).edge n a ha c3, CrystallineSemistableComparison.P.mapH_cls (cechHom m).tot n _ c3 c4]
    exact cls_congr (edge_square m hA hB n a).symm c2 c4
  constructor
  · intro x y hxy
    apply eA.1
    apply eT.1
    rw [← sq, ← sq, hxy]
  · intro y
    obtain ⟨u, hu⟩ := eT.2 ((cechAug B hB).edge.mapH n y)
    obtain ⟨x, rfl⟩ := eA.2 u
    refine ⟨x, eB.1 ?_⟩
    rw [sq, hu]

theorem mvBij : CrystallineSemistableComparison.Onto.MVBij := fun _ _ _ _ _ _ m hA hB h n => mapH_empty_bij m hA hB h n

end GlobalTheory.CompanionTheory.Onto
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSum
section
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatSpan

variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B]

theorem dpE_mul (f : W →+* B) (ξ : W) (l M i j : ℕ) :
    Lat.dpE f ξ l M i * Lat.dpE f ξ l M j =
      ((i + j).choose i : B) * Lat.dpE f ξ l M (i + j) := by
  have hc : (((i + j).choose i : ℕ) : ℚ) * ((i + j).factorial : ℚ)⁻¹ =
      ((i.factorial : ℚ))⁻¹ * ((j.factorial : ℚ))⁻¹ := by
    have h := Nat.add_choose_mul_factorial_mul_factorial i j
    rw [← Nat.choose_symm_add] at h
    have h' : (((i + j).choose i : ℕ) : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ) =
        ((i + j).factorial : ℚ) := by exact_mod_cast h
    have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    rw [← h']
    have hcne : (((i + j).choose i : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_add_right i j)).ne'
    field_simp
  unfold Lat.dpE
  rw [smul_mul_smul_comm, ← pow_add, ← hc, ← smul_smul, ← nsmul_eq_mul,
    Nat.cast_smul_eq_nsmul ℚ]

theorem mem_span_of_mem_sub (f : W →+* B) (ξ : W) (l M : ℕ) (x : B) (hx : x ∈ Lat.sub f ξ l M) :
    letI : Algebra W B := f.toAlgebra
    x ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
  letI : Algebra W B := f.toAlgebra
  have hsm : ∀ (w : W) (b : B), w • b = f w * b := fun w b => Algebra.smul_def w b
  have h0 : Lat.dpE f ξ l M 0 = 1 := by simp [Lat.dpE]
  have hgen : ∀ i, Lat.dpE f ξ l M i ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) :=
    fun i => Submodule.subset_span ⟨i, rfl⟩
  have hW : ∀ w : W, f w ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro w
    have h := Submodule.smul_mem _ w (hgen 0)
    rwa [hsm, h0, mul_one] at h
  have hnat : ∀ (n : ℕ) (y : B), y ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      (n : B) * y ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro n y hy
    have h := Submodule.smul_mem _ (n : W) hy
    rwa [hsm, map_natCast] at h
  have hmul : ∀ a b : B, a ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      b ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      a * b ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro a b ha hb
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨j, rfl⟩ := hb
        rw [dpE_mul]
        exact hnat _ _ (hgen _)
      | zero => simp
      | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
      | smul w y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ w hy
    | zero => simp
    | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
    | smul w y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ w hy
  unfold Lat.sub at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · exact hW w
    · exact hgen i
  | zero => exact Submodule.zero_mem _
  | one => rw [← h0]; exact hgen 0
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | neg y _ hy => exact Submodule.neg_mem _ hy
  | mul y z _ _ hy hz => exact hmul y z hy hz

theorem mem_sub_iff : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (x : B), x ∈ Lat.sub f ξ l M ↔
      ∃ (n : ℕ) (c : Fin n → W), x = ∑ i, f (c i) * Lat.dpE f ξ l M i := by
  intro W B _ _ _ f ξ l M x
  constructor
  · intro hx
    letI : Algebra W B := f.toAlgebra
    have hsm : ∀ (w : W) (b : B), w • b = f w * b := fun w b => Algebra.smul_def w b
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (mem_span_of_mem_sub f ξ l M x hx)
    refine ⟨c.support.sup id + 1, fun i => c i, ?_⟩
    rw [Fin.sum_univ_eq_sum_range (fun i => f (c i) * Lat.dpE f ξ l M i), Finsupp.sum]
    have hsub : c.support ⊆ Finset.range (c.support.sup id + 1) := by
      intro i hi
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
    rw [Finset.sum_congr rfl (fun i _ => hsm (c i) (Lat.dpE f ξ l M i))]
    refine Finset.sum_subset hsub fun i _ hi => ?_
    rw [Finsupp.notMem_support_iff.1 hi, map_zero, zero_mul]
  · rintro ⟨n, c, rfl⟩
    refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ ?_
    · exact Subring.subset_closure (Or.inl ⟨c i, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.LatSpan
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneResOfOneLow
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

universe w

namespace GlobalTheory.CompanionTheory.OneResProof

variable {R : Type} [CommRing R]

section Abstract

variable (D : DCx.{w} R)

def IsB (p : ℕ) : ∀ q, D.X p q → Prop
  | 0, y => y = 0
  | q + 1, y => ∃ u, D.dv p q u = y

def EZ (q : ℕ) : Prop := ∀ p (y : D.X (p + 1) q), D.dv (p + 1) q y = 0 → D.dh (p + 1) q y = 0 →
  ∃ x, D.dv p q x = 0 ∧ D.dh p q x = y

variable {D}

theorem eb (hrow : ∀ q p (u : D.X (p + 1) q), D.dh (p + 1) q u = 0 → ∃ t, D.dh p q t = u)
    {q : ℕ} (hZ : EZ D q) (p : ℕ) (u : D.X (p + 1) q) (hy : D.dh (p + 1) (q + 1) (D.dv (p + 1) q u) = 0) :
    ∃ t, D.dh p (q + 1) (D.dv p q t) = D.dv (p + 1) q u := by
  have h1 : D.dv (p + 2) q (D.dh (p + 1) q u) = 0 := by rw [← D.hv, hy]
  obtain ⟨w, hw, hw'⟩ := hZ (p + 1) (D.dh (p + 1) q u) h1 (D.hh _ _ _)
  obtain ⟨t, ht⟩ := hrow q p (u - w) (by rw [map_sub, hw', sub_self])
  exact ⟨t, by rw [D.hv, ht, map_sub, hw, sub_zero]⟩

theorem ez (hrow : ∀ q p (u : D.X (p + 1) q), D.dh (p + 1) q u = 0 → ∃ t, D.dh p q t = u) (a : ℕ)
    (hcol : ∀ p q, q ≠ a → ∀ y : D.X p q, D.dv p q y = 0 → IsB D p q y)
    (hA : ∀ p (y : D.X (p + 1) a), D.dv (p + 1) a y = 0 → D.dh (p + 1) a y = 0 →
      ∃ x, D.dv p a x = 0 ∧ IsB D (p + 1) a (y - D.dh p a x)) (q : ℕ) : EZ D q := by
  induction q with
  | zero =>
    intro p y hv hh
    by_cases h : 0 = a
    · subst h
      obtain ⟨x, hx, hb⟩ := hA p y hv hh
      exact ⟨x, hx, (sub_eq_zero.1 hb).symm⟩
    · exact ⟨0, map_zero _, by rw [map_zero]; exact (hcol _ 0 h y hv : y = 0).symm⟩
  | succ q ih =>
    intro p y hv hh
    by_cases h : q + 1 = a
    · subst h
      obtain ⟨x, hx, u, hu⟩ := hA p y hv hh
      obtain ⟨t, ht⟩ := eb hrow ih p u (by rw [hu, map_sub, hh, D.hh, sub_zero])
      exact ⟨x + D.dv p q t, by rw [map_add, hx, D.vv, add_zero], by rw [map_add, ht, hu]; abel⟩
    · obtain ⟨u, rfl⟩ : ∃ u, D.dv (p + 1) q u = y := hcol _ _ h y hv
      obtain ⟨t, ht⟩ := eb hrow ih p u hh
      exact ⟨D.dv p q t, D.vv _ _ _, ht⟩

end Abstract

variable {ι : Type} [DecidableEq ι]

theorem cech_nat {P Q : PM.{w} R ι} (φ : ∀ S, P.M S →ₗ[R] Q.M S)
    (nat : ∀ {S T : Finset ι} (h : S ⊆ T) x, φ T (P.res h x) = Q.res h (φ S x)) (p : ℕ) (x : P.cech.X p)
    (t : Fin (p + 2) → ι) : φ _ (P.cech.d p x t) = Q.cech.d p (fun i => φ _ (x i)) t := by
  rw [Cos.d_apply, Cos.d_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact nat _ _

abbrev dcx (A : Sy.{w} R ι) : DCx.{w} R where
  X p q := (A.term q).cech.X p
  dh p q := (A.term q).cech.d p
  dv p q := LinearMap.pi fun i => ((A.K (ent i)).d q).comp (LinearMap.proj i)
  hh p q := (A.term q).cech.dd p
  vv p q x := funext fun i => (A.K (ent i)).dd q (x i)
  hv p q x := funext fun t => (cech_nat (P := A.term q) (Q := A.term (q + 1)) (fun S => (A.K S).d q)
    (fun h x => (A.res h).comm _ x) p x t).symm

abbrev zpm (A : Sy.{w} R ι) (a : ℕ) : PM.{w} R ι where
  M S := (A.K S).Z a
  res h := (A.res h).mapZ a
  res_id S h x := Subtype.ext (A.res_id S h a x.1)
  res_comp h h' x := Subtype.ext (A.res_comp h h' a x.1)

theorem isB_of (A : Sy.{w} R ι) (p q : ℕ) (y : (dcx A).X p q) (h : ∀ i, y i ∈ (A.K (ent i)).B q) : IsB (dcx A) p q y := by
  cases q with
  | zero => exact funext fun i => h i
  | succ q =>
    choose u hu using h
    exact ⟨u, funext hu⟩

theorem ent_nonempty {n : ℕ} (i : Fin (n + 1) → ι) : (ent i).Nonempty :=
  ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

theorem hcol (A : Sy.{w} R ι) (a : ℕ) (hO : A.One a) (p q : ℕ) (hq : q ≠ a) (y : (dcx A).X p q)
    (hy : (dcx A).dv p q y = 0) : IsB (dcx A) p q y := by
  refine isB_of A p q y fun i => ?_
  have hs := hO (ent i) (ent_nonempty i) q hq
  have hi : (A.K (ent i)).d q (y i) = 0 := congrFun hy i
  have h0 : (Submodule.Quotient.mk ⟨y i, hi⟩ : (A.K (ent i)).H q) = 0 := Subsingleton.elim _ _
  have h2 : (⟨y i, hi⟩ : (A.K (ent i)).Z q) ∈ ((A.K (ent i)).B q).submoduleOf ((A.K (ent i)).Z q) :=
    (Submodule.Quotient.mk_eq_zero _).1 h0
  exact h2

theorem hrow (A : Sy.{w} R ι) (hD : A.Desc) (q p : ℕ) (u : (dcx A).X (p + 1) q) (hu : (dcx A).dh (p + 1) q u = 0) :
    ∃ t, (dcx A).dh p q t = u := by
  obtain ⟨t, ht⟩ := (hD q).2.2.2 p u hu
  exact ⟨t, ht.trans (one_smul _ _)⟩

theorem hA (A : Sy.{w} R ι) (a : ℕ)
    (hres : (A.coh a).cech.cx.ResUpTo 1 (LinearMap.ker ((A.coh a).cech.d 0)).subtype) (p : ℕ) (y : (dcx A).X (p + 1) a)
    (hv : (dcx A).dv (p + 1) a y = 0) (hh : (dcx A).dh (p + 1) a y = 0) :
    ∃ x, (dcx A).dv p a x = 0 ∧ IsB (dcx A) (p + 1) a (y - (dcx A).dh p a x) := by
  have natI : ∀ (p : ℕ) (z : (zpm A a).cech.X p) (t : Fin (p + 2) → ι),
      ((zpm A a).cech.d p z t).1 = (dcx A).dh p a (fun i => (z i).1) t := fun p z t =>
    cech_nat (P := zpm A a) (Q := A.term a) (fun S => ((A.K S).Z a).subtype) (fun h x => rfl) p z t
  have natQ : ∀ (p : ℕ) (z : (zpm A a).cech.X p) (t : Fin (p + 2) → ι),
      Submodule.Quotient.mk ((zpm A a).cech.d p z t) =
        (A.coh a).cech.d p (fun i => Submodule.Quotient.mk (z i)) t := fun p z t =>
    cech_nat (P := zpm A a) (Q := A.coh a) (fun S => Submodule.mkQ _) (fun h x => rfl) p z t
  let y' : (zpm A a).cech.X (p + 1) := fun i => ⟨y i, congrFun hv i⟩
  have h0 : (zpm A a).cech.d (p + 1) y' = 0 := funext fun t => Subtype.ext ((natI (p + 1) y' t).trans (congrFun hh t))
  obtain ⟨c, hc⟩ := hres.2.2.2 p (fun i => Submodule.Quotient.mk (y' i)) (funext fun t => by
    have := natQ (p + 1) y' t
    rw [h0] at this
    exact this.symm)
  have hlift : ∀ i, ∃ z : (A.K (ent i)).Z a, Submodule.Quotient.mk z = c i := fun i =>
    Submodule.Quotient.mk_surjective _ (c i)
  choose z hz using hlift
  refine ⟨fun i => (z i).1, funext fun i => (z i).2, isB_of A _ _ _ fun t => ?_⟩
  have h1 : (Submodule.Quotient.mk (y' t - (zpm A a).cech.d p z t) : (A.K (ent t)).H a) = 0 := by
    rw [Submodule.Quotient.mk_sub, natQ, sub_eq_zero]
    have e : (fun i => Submodule.Quotient.mk (z i)) = c := funext hz
    rw [e]
    exact (congrFun (hc.trans (one_smul R _)) t).symm
  have h2 := (Submodule.Quotient.mk_eq_zero _).1 h1
  have e : (y - (dcx A).dh p a fun i => (z i).1) t = (y' t - (zpm A a).cech.d p z t).1 := by
    rw [Submodule.coe_sub, natI]
    rfl
  rw [e]
  exact h2

theorem high (A : Sy.{w} R ι) (a : ℕ) (hD : A.Desc) (hO : A.One a) (hZ : ∀ q, EZ (dcx A) q) (q : ℕ) (hq : q + 1 ≠ a) :
    Subsingleton ((A.K ∅).H (q + 1)) := by
  have hall : ∀ h : (A.K ∅).H (q + 1), h = 0 := by
    intro h
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [Submodule.Quotient.mk_eq_zero]
    change x ∈ (A.K ∅).B (q + 1)
    have hx' : (A.K ∅).d (q + 1) x = 0 := hx
    have hev : (dcx A).dv 0 (q + 1) ((A.term (q + 1)).aug x) = 0 := funext fun i => by
      change (A.K (ent i)).d (q + 1) ((A.res _).f (q + 1) x) = 0
      rw [(A.res _).comm, hx', map_zero]
    obtain ⟨u, hu⟩ : ∃ u, (dcx A).dv 0 q u = (A.term (q + 1)).aug x := hcol A a hO 0 (q + 1) hq _ hev
    have hdh : (dcx A).dh 0 (q + 1) ((A.term (q + 1)).aug x) = 0 := (hD (q + 1)).1 x
    obtain ⟨v, hv, hv'⟩ := hZ q 0 ((dcx A).dh 0 q u) (by rw [← (dcx A).hv, hu, hdh]) ((dcx A).hh _ _ _)
    obtain ⟨s, hs⟩ := (hD q).2.2.1 (u - v) (by
      have : (dcx A).dh 0 q (u - v) = 0 := by rw [map_sub, hv', sub_self]
      exact this)
    rw [one_smul] at hs
    have h1 : (A.term (q + 1)).aug ((A.K ∅).d q s) = (A.term (q + 1)).aug x := by
      have e : (dcx A).dv 0 q ((A.term q).aug s) = (A.term (q + 1)).aug ((A.K ∅).d q s) :=
        funext fun i => (A.res _).comm q s
      rw [← e, hs, map_sub, hv, sub_zero, hu]
    have h2 := (hD (q + 1)).2.1 ((A.K ∅).d q s - x) (by rw [map_sub, h1, sub_self])
    rw [one_smul, sub_eq_zero] at h2
    exact ⟨s, h2⟩
  exact ⟨fun h₁ h₂ => by rw [hall h₁, hall h₂]⟩

theorem oneRes_of_oneLow : OneLow → OneRes := by
  intro hL R _ ι _ A a hD hO hres
  obtain ⟨hlow, hinj, hex⟩ := hL R ι A a hD hO
  have hZ : ∀ q, EZ (dcx A) q := ez (hrow A hD) a (hcol A a hO) (hA A a hres)
  refine ⟨fun j hj => ?_, ?_⟩
  · rcases lt_or_gt_of_ne hj with h | h
    · exact hlow j h
    · obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
      exact high A a hD hO hZ q hj
  · unfold PM.Ex Cx.ResUpTo
    refine ⟨fun x => (hex _).2 ⟨x, rfl⟩, fun x hx => ?_, fun y hy => ?_, hres.2.2.2⟩
    · rw [one_smul]
      exact hinj (hx.trans (map_zero _).symm)
    · obtain ⟨x, rfl⟩ := (hex y).1 hy
      exact ⟨x, (one_smul _ _).symm⟩

end GlobalTheory.CompanionTheory.OneResProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivCyclotomicCharacterStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_equiv_cyclotomic_character : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω), cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic | exact GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic | (intros; apply GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic <;> assumption)
end

