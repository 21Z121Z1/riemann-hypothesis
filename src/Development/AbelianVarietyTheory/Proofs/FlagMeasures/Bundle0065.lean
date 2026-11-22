import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060
import Formalism.HermitianLattices.Bundle0003
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesGoodAlmostAllPlaces
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.GoodAlmostAll

open GlobalTheory.HL.GoodClass

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
variable {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R]

theorem unitIn_one (O : Subring R) : UnitIn O 1 := ⟨O.one_mem, 1, O.one_mem, one_mul 1⟩

theorem unitIn_pow {O : Subring R} {x : R} (hx : UnitIn O x) (n : ℕ) : UnitIn O (x ^ n) := by
  induction n with
  | zero => simpa using unitIn_one O
  | succ n ih => rw [pow_succ]; exact ih.mul hx

theorem alg_mem (L : LocE K R) (x : 𝒪[K]) : algebraMap K R (x : K) ∈ L.O :=
  (L.O_def _).2 (isIntegral_algebraMap (R := 𝒪[K]) (x := x))

theorem coe_inv_unit (u : (𝒪[K])ˣ) : (((u⁻¹ : (𝒪[K])ˣ) : 𝒪[K]) : K) = ((u : 𝒪[K]) : K)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have h := congrArg (fun x : 𝒪[K] => (x : K)) u.inv_mul
  simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h
  exact h

theorem unitIn_alg (L : LocE K R) (u : (𝒪[K])ˣ) : UnitIn L.O (algebraMap K R ((u : 𝒪[K]) : K)) := by
  refine ⟨alg_mem L u, _, alg_mem L ((u⁻¹ : (𝒪[K])ˣ) : 𝒪[K]), ?_⟩
  rw [← map_mul]
  have h := congrArg (fun x : 𝒪[K] => (x : K)) u.mul_inv
  simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h
  rw [h, map_one]

theorem hf_smul (L : LocE K R) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) R) (s t : R) (x y : Fin n → R) :
    hf L Hm (s • x) (t • y) = s * L.cj t * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Local

theorem lead_scale {R R' : Type} [CommRing R] [CommRing R'] (ι : R' →+* R) {N : ℕ}
    (Z : Matrix (Fin N) (Fin N) R') (Z' : Matrix (Fin N) (Fin N) R) (β : ℕ → R)
    (h : ∀ a b, Z' a b = β b * β a * ι (Z a b)) (l : Fin (N + 1)) :
    lead Z' l = (∏ i ∈ Finset.range l, β i) ^ 2 * ι (lead Z l) := by
  unfold lead
  set e := Fin.castLE (Nat.lt_succ_iff.mp l.2)
  have h1 : Z'.submatrix e e = Matrix.of fun i j => β (e j) *
      (Matrix.of fun i j => β (e i) * ((Z.submatrix e e).map ι) i j) i j := by
    ext i j
    simp only [Matrix.submatrix_apply, h, Matrix.of_apply, Matrix.map_apply]
    ring
  rw [h1, Matrix.det_mul_row, Matrix.det_mul_column, RingHom.map_det, RingHom.mapMatrix_apply]
  have h2 : ∏ i : Fin l, β (e i) = ∏ i ∈ Finset.range l, β i := by
    rw [← Fin.prod_univ_eq_prod_range]
    rfl
  rw [h2]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))

def sc (n : ℕ) : (A.loc p).Ep :=
  algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp))⁻¹ ^ (r - n))

theorem sc_last : sc G p r = 1 := by simp [sc]

theorem cj_sc (n : ℕ) : (A.L p).cj (sc G p n) = sc G p n := (A.L p).cj.commutes _

theorem cj_ι (x : E) : (A.L p).cj ((A.loc p).ιE x) = (A.loc p).ιE (sig x) := by
  rw [A.L_cj, (A.loc p).cj_ιE]

theorem f_scale (a : Fin (r + 1)) : (G.S p).f a = sc G p a • A.bc p (G.f a) := by
  rw [sc, ← G.f_eq p a, smul_smul, ← map_mul, ← mul_pow, inv_mul_cancel₀ (G.c p).ne_zero, one_pow,
    map_one, one_smul]

theorem f'_scale (a : Fin (r + 1)) : (G.S p).f' a = sc G p a • A.bc p (G.f' a) := by
  rw [sc, ← G.f'_eq p a, smul_smul, ← map_mul, ← mul_pow, inv_mul_cancel₀ (G.c p).ne_zero, one_pow,
    map_one, one_smul]

theorem herm_bc (x y : Fin (k + 2 * r + 1) → E) :
    hf (A.L p) (G.S p).Hm (A.bc p x) (A.bc p y) = (A.loc p).ιE (∑ i, ∑ j, x i * G.Hm i j * sig (y j)) := by
  rw [G.Hm_eq p]
  exact (RatExt.rational_extend A _ p).2.2.2.2.1 G.Hm x y

theorem Zh_scale (a b : Fin (r + 1)) :
    (G.S p).Zh a b = sc G p b * sc G p a * (A.loc p).ιE (G.Zh a b) := by
  simp only [Frames.Zh, Frames.h, Matrix.of_apply, GFrames.Zh]
  rw [f_scale, f'_scale, hf_smul, cj_sc, herm_bc]

theorem D_scale (l : Fin (r + 2)) :
    (G.S p).D l = (∏ i ∈ Finset.range l, sc G p i) ^ 2 * (A.loc p).ιE (G.D l) :=
  lead_scale (A.loc p).ιE G.Zh (G.S p).Zh (sc G p) (Zh_scale G p) l

theorem TT_eq : algebraMap (A.loc p).Fp (A.loc p).Ep (((G.S p).T : (A.loc p).Fp) * (G.S p).T') =
    (A.loc p).ιE G.TT := by
  have h1 := (G.S p).gram (Fin.last r) (Fin.last r)
  have h2 := (G.S p).gram' (Fin.last r) (Fin.last r)
  simp only [and_self, if_true] at h1 h2
  rw [f_scale, Fin.val_last, sc_last, one_smul, herm_bc] at h1
  rw [f'_scale, Fin.val_last, sc_last, one_smul, herm_bc] at h2
  rw [map_mul, GFrames.TT, map_mul, h1, h2]
  ring

theorem G_scale : (G.S p).G = (∏ i ∈ Finset.range r, sc G p i) ^ 4 * (A.loc p).ιE G.Gr := by
  have hP : ∏ i ∈ Finset.range (r + 1), sc G p i = ∏ i ∈ Finset.range r, sc G p i := by
    rw [Finset.prod_range_succ, sc_last, mul_one]
  have hcj : (A.L p).cj (∏ i ∈ Finset.range r, sc G p i) = ∏ i ∈ Finset.range r, sc G p i := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => cj_sc G p i
  unfold Frames.G
  rw [D_scale, D_scale, TT_eq]
  simp only [Fin.val_last, Fin.coe_castSucc, hP, map_mul, map_pow, hcj, cj_ι, GFrames.Gr, map_sub]
  ring

end GlobalTheory.HL.GoodAlmostAll

namespace GlobalTheory.HL.GoodAlmostAll

open GlobalTheory.HL.GoodClass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

def Ok (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (x : E) : Prop :=
  (A.loc p).ιE x ∈ (A.L p).O ∧ (A.loc p).ιE x⁻¹ ∈ (A.L p).O

theorem ok_fin (A : Places F E sig) (x : E) : {p | ¬ Ok A p x}.Finite := by
  refine (((PlacesInt.integers_local A).2.1 x).union ((PlacesInt.integers_local A).2.1 x⁻¹)).subset ?_
  intro p hp
  simp only [Ok, not_and_or, Set.mem_setOf_eq] at hp
  exact hp

theorem unitIn_ok {A : Places F E sig} {p : HeightOneSpectrum (𝓞 F)} {x : E} (h : Ok A p x) (hx : x ≠ 0) :
    UnitIn (A.L p).O ((A.loc p).ιE x) :=
  ⟨h.1, _, h.2, by rw [← map_mul, mul_inv_cancel₀ hx, map_one]⟩

variable {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))

theorem unitIn_sc (u : (𝒪[(A.loc p).Fp])ˣ) (hu : ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = G.c p) (n : ℕ) :
    UnitIn (A.L p).O (sc G p n) := by
  rw [sc, map_pow, ← hu, ← coe_inv_unit]
  exact unitIn_pow (unitIn_alg (A.L p) u⁻¹) _

theorem good_of (hgg : (G.S p).gg = false) (u : (𝒪[(A.loc p).Fp])ˣ)
    (hu : ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = G.c p)
    (hHm : ∀ i j, Ok A p (G.Hm i j)) (hdet : Ok A p G.Hm.det)
    (hf : ∀ a i, Ok A p (G.f a i)) (hf' : ∀ a i, Ok A p (G.f' a i))
    (hes : ∀ a i, Ok A p (G.es a i)) (hes' : ∀ a i, Ok A p (G.es' a i))
    (hD : ∀ l, Ok A p (G.D l)) (hGr : Ok A p G.Gr) : Good (G.S p) := by
  haveI := PlacesInt.nontrivial_Ep (A.loc p)
  have hc : UnitIn (A.L p).O (algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p)) := hu ▸ unitIn_alg (A.L p) u
  have hP : ∀ n, UnitIn (A.L p).O (∏ i ∈ Finset.range n, sc G p i) := fun n =>
    unitIn_prod _ _ _ fun i _ => unitIn_sc G p u hu i
  refine ⟨hgg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [G.Hm_eq p]
    exact (hHm i j).1
  · have hdet' : (G.S p).Hm.det = (A.loc p).ιE G.Hm.det := by
      rw [G.Hm_eq p, RingHom.map_det, RingHom.mapMatrix_apply]
    have hne : G.Hm.det ≠ 0 := by
      intro h0
      have := (G.S p).herm.2
      rw [hdet', h0, map_zero] at this
      exact not_isUnit_zero this
    obtain ⟨-, y, hy, hxy⟩ := unitIn_ok hdet hne
    exact ⟨y, hy, hdet' ▸ hxy⟩
  · intro a i
    rw [f_scale G p a]
    exact (A.L p).O.mul_mem (unitIn_sc G p u hu a).1 (hf a i).1
  · intro a i
    rw [f'_scale G p a]
    exact (A.L p).O.mul_mem (unitIn_sc G p u hu a).1 (hf' a i).1
  · intro a i
    rw [G.es_eq p a]
    exact (A.L p).O.mul_mem (by rw [map_pow]; exact (unitIn_pow hc _).1) (hes a i).1
  · intro a i
    rw [G.es'_eq p a]
    exact (A.L p).O.mul_mem (by rw [map_pow]; exact (unitIn_pow hc _).1) (hes' a i).1
  · have hne : G.Gr ≠ 0 := by
      intro h0
      apply (G.S p).G_ne
      change (G.S p).G = 0
      rw [G_scale, h0, map_zero, mul_zero]
    have := (unitIn_pow (hP r) 4).mul (unitIn_ok hGr hne)
    rw [← G_scale] at this
    exact this
  · intro l hl
    have hne : G.D l ≠ 0 := by
      intro h0
      apply hl
      rw [D_scale, h0, map_zero, mul_zero]
    have := (unitIn_pow (hP l) 2).mul (unitIn_ok (hD l) hne)
    rw [← D_scale] at this
    exact this

end GlobalTheory.HL.GoodAlmostAll

theorem GlobalTheory.HL.StdPlace.good_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), {p | ¬ Good (G.S p)}.Finite := by
  intro F E _ _ _ _ _ sig A r k G
  open GlobalTheory.HL.GoodAlmostAll in
  have H : ({p | (G.S p).gg = true} ∪
      {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = G.c p} ∪
      (⋃ i, ⋃ j, {p | ¬ Ok A p (G.Hm i j)}) ∪ {p | ¬ Ok A p G.Hm.det} ∪
      (⋃ a, ⋃ i, {p | ¬ Ok A p (G.f a i)}) ∪ (⋃ a, ⋃ i, {p | ¬ Ok A p (G.f' a i)}) ∪
      (⋃ a, ⋃ i, {p | ¬ Ok A p (G.es a i)}) ∪ (⋃ a, ⋃ i, {p | ¬ Ok A p (G.es' a i)}) ∪
      (⋃ l, {p | ¬ Ok A p (G.D l)}) ∪ {p | ¬ Ok A p G.Gr}).Finite := by
    refine (((((((((G.gg_fin.union G.c_unit).union ?_).union (ok_fin A _)).union ?_).union ?_).union ?_).union
      ?_).union ?_).union (ok_fin A _))
    all_goals first
      | exact Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => ok_fin A _
      | exact Set.finite_iUnion fun _ => ok_fin A _
  refine H.subset fun p hp => ?_
  by_contra hB
  apply hp
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_not,
    Bool.not_eq_true] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hgg, hu⟩, hHm⟩, hdet⟩, hf⟩, hf'⟩, hes⟩, hes'⟩, hD⟩, hGr⟩ := hB
  obtain ⟨u, hu⟩ := not_forall_not.mp hu
  exact GlobalTheory.HL.GoodAlmostAll.good_of G p hgg u hu hHm hdet hf hf' hes hes' hD hGr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesDatumMoveProperties
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveFacts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem conj_form {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x y : Fin n → E) : hf L Hm y x = L.cj (hf L Hm x y) := by
  have h' : cT L Hm = Hm := h
  have hH : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun h' j) i
  unfold hf
  simp_rw [map_sum, map_mul, L.cj_cj, hH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem hf_add_left_flag_measures' (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x x' y : Fin n → E) : hf L Hm (x + x') y = hf L Hm x y + hf L Hm x' y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hf_smul_left_flag_measures' (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (c : E) (x y : Fin n → E) : hf L Hm (c • x) y = c * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem hf_zero_left_flag_measures (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (y : Fin n → E) : hf L Hm 0 y = 0 := by
  simp [hf]

theorem form_zero_of_span {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (A : Set (Fin n → E)) (hA : ∀ a ∈ A, ∀ b ∈ A, hf L Hm a b = 0) :
    ∀ x ∈ Submodule.span E A, ∀ y ∈ Submodule.span E A, hf L Hm x y = 0 := by
  intro x hx y hy
  have h1 : ∀ a ∈ A, ∀ z ∈ Submodule.span E A, hf L Hm z a = 0 := by
    intro a ha z hz
    induction hz using Submodule.span_induction with
    | mem w hw => exact hA w hw a ha
    | zero => exact hf_zero_left_flag_measures L Hm a
    | add u v _ _ hu hv => rw [hf_add_left_flag_measures', hu, hv, add_zero]
    | smul c u _ hu => rw [hf_smul_left_flag_measures', hu, mul_zero]
  induction hx using Submodule.span_induction with
  | mem w hw => rw [conj_form h y w, h1 w hw y hy, map_zero]
  | zero => exact hf_zero_left_flag_measures L Hm y
  | add u v _ _ hu hv => rw [hf_add_left_flag_measures', hu, hv, add_zero]
  | smul c u _ hu => rw [hf_smul_left_flag_measures', hu, mul_zero]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j := by
  unfold Frames.spanTo
  exact Submodule.span_mono (Set.image_mono fun a (ha : (a : ℕ) < i) => lt_of_lt_of_le ha h)

theorem iso_spanTo (g : Fin (r + 1) → S.V) (c : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then c else 0)
    (x : S.V) (hx : x ∈ S.spanTo g r) : S.h x x = 0 := by
  have hH : IsHerm L S.Hm := S.herm.1
  show hf L S.Hm x x = 0
  refine form_zero_of_span hH (g '' {i | (i : ℕ) < r}) ?_ x hx x hx
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have ha' : (a : ℕ) < r := ha
  have hne : a ≠ Fin.last r := fun e => by subst e; simp at ha'
  rw [hg, if_neg (fun hc => hne hc.1)]

theorem mem_span_frame (g : Fin (r + 1) → S.V) (n : S.GLV) (hn : n ∈ S.Nof g) (j : Fin r)
    (x : S.V) (hx : x ∈ S.spanTo g (j + 1)) :
    x ∈ Submodule.span E (Set.range fun b => n (g b)) := by
  have key : ∀ m : ℕ, m ≤ r → S.spanTo g m ≤ Submodule.span E (Set.range fun b => n (g b)) := by
    intro m
    induction m with
    | zero =>
      intro _
      unfold Frames.spanTo
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact absurd (show (i : ℕ) < 0 from hi) (Nat.not_lt_zero _)
    | succ m ih =>
      intro hm
      have hm' : m < r := by omega
      have h0 : n ∈ S.Nof g := hn
      unfold Frames.Nof at h0
      have hI := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp h0).1).2
      have hU : n ∈ unipOn (S.spanTo g (m + 1)) (S.spanTo g m) := Subgroup.mem_iInf.mp hI ⟨m, hm'⟩
      have hU' : (∀ v, n v ∈ S.spanTo g (m + 1) ↔ v ∈ S.spanTo g (m + 1)) ∧
          ∀ v ∈ S.spanTo g (m + 1), n v - v ∈ S.spanTo g m := hU
      have hsub : S.spanTo g (m + 1) ≤ Submodule.span E (Set.range fun b => n (g b)) := by
        unfold Frames.spanTo
        rw [Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        have hgi : g i ∈ S.spanTo g (m + 1) := Submodule.subset_span ⟨i, hi, rfl⟩
        have h2 := ih hm'.le (hU'.2 (g i) hgi)
        have h3 : n (g i) ∈ Submodule.span E (Set.range fun b => n (g b)) :=
          Submodule.subset_span ⟨i, rfl⟩
        have h4 := Submodule.sub_mem _ h3 h2
        rwa [sub_sub_cancel] at h4
      exact hsub
  exact key (j + 1) (Nat.succ_le_of_lt j.2) hx

theorem parts_of_mem_Mof (hth : S.th ≠ 0) (hO : algebraMap F E S.th ∈ L.O)
    (g g' : Fin (r + 1) → S.V) (m : S.V) (hm : m ∈ S.Mof g g') :
    ∃ ξ ∈ Submodule.span L.O (Set.range g), ∃ ξ' ∈ Submodule.span L.O (Set.range g'),
      algebraMap F E S.th • m = ξ + ξ' := by
  have hinv : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hth, map_one]
  unfold Frames.Mof at hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · refine ⟨algebraMap F E S.th • g b, ?_, 0, zero_mem _, by rw [add_zero]⟩
      exact Submodule.smul_mem _ (⟨algebraMap F E S.th, hO⟩ : L.O) (Submodule.subset_span ⟨b, rfl⟩)
    · refine ⟨-g b, neg_mem (Submodule.subset_span ⟨b, rfl⟩), g' b, Submodule.subset_span ⟨b, rfl⟩, ?_⟩
      show algebraMap F E S.th • algebraMap F E S.th⁻¹ • (g' b - g b) = -g b + g' b
      rw [smul_smul, hinv, one_smul, sub_eq_neg_add]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, a', ha', e⟩ := hu
    obtain ⟨b, hb, b', hb', e'⟩ := hv
    exact ⟨a + b, add_mem ha hb, a' + b', add_mem ha' hb', by rw [smul_add, e, e']; abel⟩
  | smul c u _ hu =>
    obtain ⟨a, ha, a', ha', e⟩ := hu
    refine ⟨c • a, Submodule.smul_mem _ c ha, c • a', Submodule.smul_mem _ c ha', ?_⟩
    show algebraMap F E S.th • ((c : E) • u) = (c : E) • a + (c : E) • a'
    rw [smul_smul, mul_comm (algebraMap F E S.th) (c : E), ← smul_smul, e, smul_add]

theorem move_facts : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → s • x ∈ Λ ∧ L.cj s • x ∈ Λ ∧ s • x' ∈ Λ ∧ L.cj s • x' ∈ Λ ∧ (∃ c ∈ L.O, S.h x' x = algebraMap F E S.th * c) ∧ S.h x x = 0 ∧ S.h x' x' = 0 ∧ S.h u x = 0 ∧ S.h u x' = 0 ∧ x ∈ S.X ∧ x' ∈ S.X' := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hM
  obtain ⟨hx, hx', hin, -, -, huperp, ⟨c, hcO, hs⟩, -⟩ := hM
  obtain ⟨y, hyΛ, hxy⟩ := id hin
  obtain ⟨⟨-, -, hint⟩, -⟩ := hF
  have hj : (j : ℕ) + 1 ≤ r := Nat.succ_le_of_lt j.2
  have hxX : x ∈ S.X := spanTo_mono S S.f hj hx
  have hx'X : x' ∈ S.X' := spanTo_mono S S.f' hj hx'
  have hH : IsHerm L S.Hm := S.herm.1
  have hxx : S.h x x = 0 := iso_spanTo S S.f _ S.gram x hxX
  have hx'x' : S.h x' x' = 0 := iso_spanTo S S.f' _ S.gram' x' hx'X
  have hperp : ∀ z ∈ S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1), hf L S.Hm u z = 0 := huperp
  have hux : S.h u x = 0 := hperp x (Submodule.mem_sup_left hx)
  have hux' : S.h u x' = 0 := hperp x' (Submodule.mem_sup_right hx')
  obtain ⟨c0, hc0, he⟩ := hint x hxX x' hx'X x hxX x' hx'X hin hin
  have he' : hf L S.Hm x x' = algebraMap F E S.th * c0 := he
  have hcross : S.h x' x = algebraMap F E S.th * L.cj c0 := by
    show hf L S.Hm x' x = _
    rw [conj_form hH x x', he', map_mul, AlgEquiv.commutes]
  obtain ⟨-, hW, -, hfrL, hfr'L, hli, -, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hn, hn', -⟩ := hW
  obtain ⟨-, -, -, -, -, hth, hthO, -⟩ := GlobalTheory.FrameBasic.frames_basic L r k S
  obtain ⟨-, -, -, -, -, -, -, -, hMa, -, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT
  have hthE : algebraMap F E S.th ∈ L.O := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).mpr hthO
  have hinv : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hth, map_one]
  have hsum : x + x' ∈ S.ME :=
    add_mem (Submodule.mem_sup_left (spanTo_mono S S.f (by omega) hx))
      (Submodule.mem_sup_right (spanTo_mono S S.f' (by omega) hx'))
  have hyeq : y = algebraMap F E S.th⁻¹ • (x + x') := by
    rw [hxy, smul_smul, hinv, one_smul]
  have hyME : y ∈ S.ME := by rw [hyeq]; exact Submodule.smul_mem _ _ hsum
  have hysat : y ∈ S.sat Λ := Submodule.mem_inf.mpr ⟨hyΛ, hyME⟩
  obtain ⟨ξ, hξ, ξ', hξ', hsplit⟩ :=
    parts_of_mem_Mof S hth hthE (S.fr d Λ) (S.fr' d Λ) _ (hMa y hysat)
  set P := algebraMap F E ((S.ϖ : F) ^ S.a) with hP
  have hsplit' : P • x + P • x' = ξ + ξ' := by
    rw [← smul_add, hxy, smul_comm]; exact hsplit
  have hxfr : x ∈ Submodule.span E (Set.range (S.fr d Λ)) :=
    mem_span_frame S S.f (S.wit d Λ).1 hn j x hx
  have hx'fr : x' ∈ Submodule.span E (Set.range (S.fr' d Λ)) :=
    mem_span_frame S S.f' (S.wit d Λ).2 hn' j x' hx'
  have hdis := (linearIndependent_sum.mp hli).2.2
  have hw1 : P • x - ξ ∈ Submodule.span E (Set.range (S.fr d Λ)) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hxfr)
      (Submodule.span_le_restrictScalars L.O E _ hξ)
  have hw2 : P • x - ξ ∈ Submodule.span E (Set.range (S.fr' d Λ)) := by
    have e : P • x - ξ = ξ' - P • x' := by
      rw [sub_eq_sub_iff_add_eq_add, hsplit', add_comm]
    rw [e]
    exact Submodule.sub_mem _ (Submodule.span_le_restrictScalars L.O E _ hξ')
      (Submodule.smul_mem _ _ hx'fr)
  have hPx : P • x = ξ := sub_eq_zero.mp ((Submodule.disjoint_def.mp hdis) _ hw1 hw2)
  have hPx' : P • x' = ξ' := by rw [hPx] at hsplit'; exact add_left_cancel hsplit'
  have hfrΛ : ∀ b, S.fr d Λ b ∈ Λ := fun b =>
    ((hfrL (r + 1) le_rfl (S.fr d Λ b)).mpr (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
  have hfr'Λ : ∀ b, S.fr' d Λ b ∈ Λ := fun b =>
    ((hfr'L (r + 1) le_rfl (S.fr' d Λ b)).mpr (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
  have hξΛ : ξ ∈ Λ := Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact hfrΛ b) hξ
  have hξ'Λ : ξ' ∈ Λ := Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact hfr'Λ b) hξ'
  have key : ∀ z, P • z ∈ Λ → s • z ∈ Λ ∧ L.cj s • z ∈ Λ := by
    intro z hz
    have hc' : L.cj c ∈ L.O := GlobalTheory.UnramOrder.cj_mem L hcO
    have h1 : s • z = (⟨c, hcO⟩ : L.O) • (P • z) := by
      rw [hs]; show (P * c) • z = c • (P • z); rw [smul_smul, mul_comm c P]
    have h2 : L.cj s • z = (⟨L.cj c, hc'⟩ : L.O) • (P • z) := by
      rw [hs, map_mul, AlgEquiv.commutes]; show (P * L.cj c) • z = L.cj c • (P • z)
      rw [smul_smul, mul_comm (L.cj c) P]
    exact ⟨h1 ▸ Λ.smul_mem _ hz, h2 ▸ Λ.smul_mem _ hz⟩
  have kx := key x (hPx ▸ hξΛ)
  have kx' := key x' (hPx' ▸ hξ'Λ)
  exact ⟨kx.1, kx.2, kx'.1, kx'.2, ⟨L.cj c0, GlobalTheory.UnramOrder.cj_mem L hc0, hcross⟩, hxx, hx'x',
    hux, hux', hxX, hx'X⟩

end GlobalTheory.HL.MoveFacts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RegulatorLeSumSmallIdealsInClassStatement
section
open MeasureTheory NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regulator_le_sum_small_ideals_in_class : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ (C : ClassGroup (𝓞 K)) (S : Finset (Ideal (𝓞 K))), (∀ I, I ∈ S ↔ ∃ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)), ClassGroup.mk0 ⟨I, hI⟩ = C ∧ (Ideal.absNorm I : ℝ) ≤ Real.sqrt |(discr K : ℝ)|) → Units.regulator K ≤ ∑ I ∈ S, Real.log (Real.sqrt |(discr K : ℝ)| / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ) := by
  first | exact @GlobalTheory.RegulatorClassBound.regulator_le_sum_class | exact GlobalTheory.RegulatorClassBound.regulator_le_sum_class | (intros; apply GlobalTheory.RegulatorClassBound.regulator_le_sum_class <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexSpanLatticeMatrixDetNormStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_span_lattice_matrix_det_norm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ {n m : ℕ} (b : Fin m → Fin n → E), LinearIndependent E b → ∀ (A : Matrix (Fin m) (Fin m) E) (c : F), c ≠ 0 → A.det * L.cj A.det = algebraMap F E c → ∀ Q Q' : Submodule L.O (Fin n → E), Q = Submodule.span L.O (Set.range b) → Q' = Submodule.span L.O (Set.range fun j => ∑ i, A i j • b i) → Q'.toAddSubgroup.relIndex Q.toAddSubgroup ≠ 0 ∧ Q.toAddSubgroup.relIndex Q'.toAddSubgroup ≠ 0 ∧ (Q'.toAddSubgroup.relIndex Q.toAddSubgroup : ℝ) = (resQ ϖ : ℝ) ^ (vE L ϖ (algebraMap F E c)) * (Q.toAddSubgroup.relIndex Q'.toAddSubgroup : ℝ) := by
  first | exact @GlobalTheory.HL.FrameIndex.relIndex_span_matrix | exact GlobalTheory.HL.FrameIndex.relIndex_span_matrix | (intros; apply GlobalTheory.HL.FrameIndex.relIndex_span_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZeroStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrame_gram_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → (gramE σ J (tupH P)).det ≠ 0 ∧ (∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) ∧ (∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j) ∧ (∀ i j, gramE σ J (F0 P) i j = if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) ∧ ∀ v : HeightOneSpectrum (𝓞 F), LinearIndependent (Fv F v ⊗[F] E) (ratTup (F := F) (Fv F v) (F0 P)) := by
  first | exact @GlobalTheory.FrameGram.std_frame_gram | exact GlobalTheory.FrameGram.std_frame_gram | (intros; apply GlobalTheory.FrameGram.std_frame_gram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupOrthogonalComplementUnimodularStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_orthogonalComplement_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ Λ0 Λ : Submodule L.O (Fin n → E), IsLat L Λ0 → IsLat L Λ → ∀ h ∈ fixG L Hm (Submodule.span E (Set.range x)), invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0) (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L (h • Λ)) = invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0) (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ) := by
  first | exact @GlobalTheory.HL.Unimod.unimodular | exact GlobalTheory.HL.Unimod.unimodular | (intros; apply GlobalTheory.HL.Unimod.unimodular <;> assumption)
end

