import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.EtaleCohomology.TateTwists.Bundle0001
import Development.EtaleCohomology.TateTwists.Bundle0005
import Development.EtaleCohomology.KummerTheory.Bundle0001
import Development.EtaleCohomology.TateTwists.Bundle0002

-- bundled from Development.EtaleCohomology.TateTwists.CupGradedCommOfFlip
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def cupflip_wd : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
    ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+
        CohomologyClass ((chains R).obj E) K k,
      ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k), μ.IsAW hk α.1 β.1 γ.1 →
        c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def cupflip_aw_exists : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
    ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1

def cupflip_aw_flip : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν →
    ∀ (E : Spc) {n m k : ℤ} (h : n + m = k) (h' : m + n = k)
      (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
      (γ γ' : Cocycle ((chains R).obj E) K k),
      μ.IsAW h α.1 β.1 γ.1 → ν.IsAW h' β.1 α.1 γ'.1 →
        CohomologyClass.mk γ = (n * m).negOnePow • CohomologyClass.mk γ'

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.CyclotomicPrimitiveRootProductIdentitiesOfAdjoin
section
open Polynomial Finset GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.PrimPf

noncomputable def μ (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

lemma hμ (q : ℕ) [NeZero q] : IsPrimitiveRoot (μ q) q :=
  Complex.isPrimitiveRoot_exp q (NeZero.ne q)

lemma aeval_cyc {n : ℕ} (hn : 0 < n) {ν : ℂ} (h : IsPrimitiveRoot ν n) :
    aeval ν (cyclotomic n ℤ) = 0 := by
  rw [cyclotomic_eq_minpoly h hn]; exact minpoly.aeval _ _

lemma hom_aeval {S T : Type} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (f : S →+* T) (x : S) (p : ℤ[X]) :
    f (aeval x p) = aeval (f x) p := by
  rw [aeval_def, aeval_def, hom_eval₂]; congr 1; exact RingHom.ext_int _ _

abbrev R (q : ℕ) := AdjoinRoot (cyclotomic q ℤ)

noncomputable abbrev θ (q : ℕ) : R q := AdjoinRoot.root (cyclotomic q ℤ)

noncomputable def φ (q : ℕ) [NeZero q] : R q →+* ℂ :=
  AdjoinRoot.lift (algebraMap ℤ ℂ) (μ q) (by rw [← aeval_def]; exact aeval_cyc (NeZero.pos q) (hμ q))

lemma φ_root (q : ℕ) [NeZero q] : φ q (θ q) = μ q := AdjoinRoot.lift_root _

lemma φ_inj (q : ℕ) [NeZero q] : Function.Injective (φ q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [AdjoinRoot.mk_eq_zero]
  have h : aeval (μ q) p = 0 := by
    rw [φ, AdjoinRoot.lift_mk] at hx; rwa [aeval_def]
  rw [cyclotomic_eq_minpoly (hμ q) (NeZero.pos q)]
  exact minpoly.isIntegrallyClosed_dvd ((hμ q).isIntegral (NeZero.pos q)) h

noncomputable def ψ {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : R q →+* A :=
  AdjoinRoot.lift (algebraMap ℤ A) ζ.1 (by rw [← aeval_def]; exact ζ.2.2)

lemma ψ_root {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ψ ζ (θ q) = ζ.1 :=
  AdjoinRoot.lift_root _

lemma θ_pow (q : ℕ) [NeZero q] : θ q ^ q = 1 :=
  φ_inj q (by rw [map_pow, φ_root, map_one, (hμ q).pow_eq_one])

lemma root_of_prim {q r a : ℕ} [NeZero q] (hr : 0 < r) (h : IsPrimitiveRoot (μ q ^ a) r) :
    aeval (θ q ^ a) (cyclotomic r ℤ) = 0 :=
  φ_inj q (by rw [hom_aeval (φ q), map_pow, φ_root, map_zero]; exact aeval_cyc hr h)

lemma image_range (q : ℕ) [NeZero q] :
    (range q).image (fun a => μ q ^ a) = nthRootsFinset q (1 : ℂ) := by
  ext x
  rw [mem_image, mem_nthRootsFinset (NeZero.pos q)]
  constructor
  · rintro ⟨a, -, rfl⟩; rw [← pow_mul, mul_comm, pow_mul, (hμ q).pow_eq_one, one_pow]
  · intro hx
    obtain ⟨i, hi, rfl⟩ := (hμ q).eq_pow_of_pow_eq_one hx
    exact ⟨i, mem_range.2 hi, rfl⟩

lemma image_prim (q : ℕ) [NeZero q] :
    ((range q).filter (fun a => Nat.Coprime a q)).image (fun a => μ q ^ a) = primitiveRoots q ℂ := by
  ext x
  rw [mem_image, mem_primitiveRoots (NeZero.pos q)]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact (hμ q).pow_of_coprime a (mem_filter.1 ha).2
  · intro hx
    obtain ⟨i, hi, rfl⟩ := (hμ q).eq_pow_of_pow_eq_one hx.pow_eq_one
    exact ⟨i, mem_filter.2 ⟨mem_range.2 hi, ((hμ q).pow_iff_coprime (NeZero.pos q) i).1 hx⟩, rfl⟩

lemma inj_on (q : ℕ) [NeZero q] (s : Finset ℕ) (hs : s ⊆ range q) :
    Set.InjOn (fun a => μ q ^ a) s := by
  intro i hi j hj h
  exact (hμ q).pow_inj (mem_range.1 (hs hi)) (mem_range.1 (hs hj)) h

lemma C_prod_all (q : ℕ) [NeZero q] :
    ∏ a ∈ range q, (X - C (μ q ^ a)) = (X ^ q - 1 : ℂ[X]) := by
  rw [X_pow_sub_one_eq_prod (NeZero.pos q) (hμ q), ← image_range,
    prod_image (inj_on q _ subset_rfl)]

lemma C_prod_prim (q : ℕ) [NeZero q] :
    ∏ a ∈ (range q).filter (fun a => Nat.Coprime a q), (X - C (μ q ^ a)) = cyclotomic q ℂ := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (hμ q), ← image_prim,
    prod_image (inj_on q _ (filter_subset _ _))]

lemma mapφ_C_prod (q : ℕ) [NeZero q] (s : Finset ℕ) :
    (∏ a ∈ s, (X - C (θ q ^ a))).map (φ q) = ∏ a ∈ s, (X - C (μ q ^ a)) := by
  simp [Polynomial.map_prod, φ_root]

lemma R_prod_all (q : ℕ) [NeZero q] :
    ∏ a ∈ range q, (X - C (θ q ^ a)) = (X ^ q - 1 : (R q)[X]) := by
  apply Polynomial.map_injective _ (φ_inj q)
  rw [mapφ_C_prod, C_prod_all]; simp

lemma R_prod_prim (q : ℕ) [NeZero q] :
    ∏ a ∈ (range q).filter (fun a => Nat.Coprime a q), (X - C (θ q ^ a))
      = (cyclotomic q ℤ).map (algebraMap ℤ (R q)) := by
  apply Polynomial.map_injective _ (φ_inj q)
  rw [mapφ_C_prod, C_prod_prim, Polynomial.map_map, ← map_cyclotomic_int]
  congr 1; exact RingHom.ext_int _ _

lemma C_prod_geom (n : ℕ) [NeZero (n + 1)] :
    ∏ i ∈ range n, (X - C (μ (n + 1) ^ (i + 1))) = ∑ i ∈ range (n + 1), (X ^ i : ℂ[X]) := by
  have h := C_prod_all (n + 1)
  rw [prod_range_succ', pow_zero, ← geom_sum_mul, C_1] at h
  have hne : (X - 1 : ℂ[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ℂ)
  exact mul_right_cancel₀ hne h

lemma R_prod_geom (n : ℕ) [NeZero (n + 1)] :
    ∏ i ∈ range n, (X - C (θ (n + 1) ^ (i + 1))) = ∑ i ∈ range (n + 1), (X ^ i : (R (n + 1))[X]) := by
  apply Polynomial.map_injective _ (φ_inj (n + 1))
  simp only [Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, map_pow, φ_root, Polynomial.map_pow]
  simpa using C_prod_geom n

lemma eval_prod_ψ {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) (y : A) (s : Finset ℕ) (f : ℕ → ℕ) :
    eval₂ (ψ ζ) y (∏ a ∈ s, (X - C (θ q ^ f a))) = ∏ a ∈ s, (y - ζ.1 ^ f a) := by
  simp [eval₂_finsetProd, eval₂_pow, ψ_root]

lemma eval_prod_ψ0 {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) (y : A) (s : Finset ℕ) :
    eval₂ (ψ ζ) y (∏ a ∈ s, (X - C (θ q ^ a))) = ∏ a ∈ s, (y - ζ.1 ^ a) := by
  simp [eval₂_finsetProd, eval₂_pow, ψ_root]

lemma unit_prod {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ i ∈ range (q - 1), (1 - ζ.1 ^ (i + 1)) = (q : A) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos q)).symm⟩
  have h := congrArg (eval₂ (ψ ζ) 1) (R_prod_geom n)
  rw [eval_prod_ψ ζ 1 _ (fun i => i + 1)] at h
  simpa [eval₂_finsetSum] using h

theorem cyclotomic_primitive_root_product_identities_of_adjoin_root : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := by
  intro q _ A _
  have hq1 : ∀ ζ : Prim q A, ζ.1 ^ q = 1 := fun ζ => by
    rw [← ψ_root, ← map_pow, θ_pow, map_one]
  have hu : ∀ ζ : Prim q A, IsUnit ζ.1 := fun ζ =>
    IsUnit.of_mul_eq_one (ζ.1 ^ (q - 1)) (by
      rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos q), hq1])
  have hmod : ∀ (ζ : Prim q A) (a : ℕ), ζ.1 ^ a = ζ.1 ^ (a % q) := fun ζ a => by
    conv_lhs => rw [← Nat.mod_add_div a q, pow_add, pow_mul, hq1, one_pow, mul_one]
  have hlt : ∀ (ζ : Prim q A) (c d : ℕ), c < d → d < q → IsUnit (ζ.1 ^ c - ζ.1 ^ d) := by
    intro ζ c d hcd hd
    obtain ⟨i, rfl⟩ : ∃ i, d = c + (i + 1) := ⟨d - c - 1, by omega⟩
    have e : ζ.1 ^ c - ζ.1 ^ (c + (i + 1)) = ζ.1 ^ c * (1 - ζ.1 ^ (i + 1)) := by ring
    rw [e]
    refine ((hu ζ).pow c).mul (isUnit_of_dvd_unit ?_ ζ.2.1)
    have hd := dvd_prod_of_mem (fun j => 1 - ζ.1 ^ (j + 1)) (mem_range.2 (show i < q - 1 by omega))
    rw [unit_prod ζ] at hd
    exact hd
  refine ⟨hq1, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ a ha
    refine ⟨⟨ζ.1 ^ a, ζ.2.1, ?_⟩, rfl⟩
    rw [← ψ_root, ← map_pow, ← hom_aeval (ψ ζ),
      root_of_prim (NeZero.pos q) ((hμ q).pow_of_coprime a ha), map_zero]
  · intro ζ a b hab
    rw [hmod ζ a, hmod ζ b]
    have hne : a % q ≠ b % q := hab
    have ha := Nat.mod_lt a (NeZero.pos q)
    have hb := Nat.mod_lt b (NeZero.pos q)
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt ζ _ _ h hb
    · have := (hlt ζ _ _ h ha).neg
      rwa [neg_sub] at this
  · intro ζ x hx
    have h := congrArg (eval₂ (ψ ζ) x) (R_prod_all q)
    rw [eval_prod_ψ0] at h
    simpa [hx] using h
  · intro ζ ξ
    have h := congrArg (eval₂ (ψ ζ) ξ.1) (R_prod_prim q)
    rw [eval_prod_ψ0, eval₂_map] at h
    rw [h]
    have e : (ψ ζ).comp (algebraMap ℤ (R q)) = algebraMap ℤ A := RingHom.ext_int _ _
    rw [e, ← aeval_def]; exact ξ.2.2
  · intro r hr ζ
    have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hr (NeZero.pos q)
    have hur : IsUnit (r : A) := by
      obtain ⟨k, hk⟩ := hr
      have := ζ.2.1
      rw [hk, Nat.cast_mul] at this
      exact isUnit_of_mul_isUnit_left this
    refine ⟨⟨ζ.1 ^ (q / r), hur, ?_⟩, rfl⟩
    rw [← ψ_root, ← map_pow, ← hom_aeval (ψ ζ),
      root_of_prim hr0 ((hμ q).pow (NeZero.pos q) (Nat.div_mul_cancel hr).symm), map_zero]

end LateralTheory.EtaleFoundations.PrimPf
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupLeibnizOfPairing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW

namespace LateralTheory.EtaleFoundations.AWLeib
variable {R : Type} [CommRing R]

theorem bd_map {E : Spc} {U : Scheme.{0}} {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (φ : G →+ G')
    (f : ∀ p : ℕ, Sx E p U → G) (p : ℕ) (y : Sx E p U) : φ (bd f p y) = bd (fun q z => φ (f q z)) p y := by
  cases p with
  | zero => simp [bd]
  | succ p => simp [bd, map_sum, map_zsmul]

theorem ev_delta_bd {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (p : ℕ)
    (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + m = t) (U : Scheme.{0}) (x : Sx E p U) :
    ev (δ n m α) p t ht U x = Sec.map (I.d s t) (ev α p s hs U x) +
      m.negOnePow • bd (fun q z => if hh : -(q : ℤ) + n = t then ev α q t hh U z else 0) p x := by
  cases p with
  | zero => rw [ev_delta_zero hm α s t hs ht U x]; simp [bd]
  | succ p =>
    rw [ev_delta_succ hm α p s t hs ht U x]
    congr 2
    simp only [bd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dif_pos (by omega)]

theorem mul_congr {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) {E : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (p q : ℕ) (y : Sx E p U) (z : Sx E q U)
    (s t w s' t' : ℤ) (h : s + t = w) (h' : s' + t' = w) (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t)
    (hs' : -(p : ℤ) + n = s') (ht' : -(q : ℤ) + m = t') :
    μ.mul U s t w h (ev α p s hs U y) (ev β q t ht U z) = μ.mul U s' t' w h' (ev α p s' hs' U y) (ev β q t' ht' U z) := by
  subst hs ht hs' ht'; rfl

theorem leib' {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w s' t' w' : ℤ) (h : s + t = w) (hs : s + 1 = s')
    (ht : t + 1 = t') (hw : w + 1 = w') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (K.d w w') (μ.mul U s t w h a b) = μ.mul U s' t w' (by omega) (Sec.map (I.d s s') a) b +
      s.negOnePow • μ.mul U s t' w' (by omega) a (Sec.map (J.d t t') b) := by
  subst hs ht hw; exact μ.leibniz U s t w h a b

theorem mul_bd_left {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (f : ∀ q : ℕ, Sx E q U → Sec (I.X s) U) (p : ℕ) (y : Sx E p U) (b : Sec (J.X t) U) :
    μ.mul U s t w h (bd f p y) b = bd (fun q z => μ.mul U s t w h (f q z) b) p y :=
  bd_map (((μ.mul U s t w h).flip b).toAddMonoidHom) f p y

theorem mul_bd_right {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (f : ∀ q : ℕ, Sx E q U → Sec (J.X t) U) (p : ℕ) (y : Sx E p U) (a : Sec (I.X s) U) :
    μ.mul U s t w h a (bd f p y) = bd (fun q z => μ.mul U s t w h a (f q z)) p y :=
  bd_map ((μ.mul U s t w h a).toAddMonoidHom) f p y

theorem secmap_sum {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type*} (s : Finset ι) (f : ι → Sec F U) :
    Sec.map φ (∑ i ∈ s, f i) = ∑ i ∈ s, Sec.map φ (f i) := map_sum ((φ.hom.app (op U)).hom) f s

theorem secmap_zsmul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℤ) (a : Sec F U) :
    Sec.map φ (c • a) = c • Sec.map φ a := map_zsmul ((φ.hom.app (op U)).hom) c a

def Fm {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m : ℤ} (α : Cochain ((chains R).obj E) I n)
    (β : Cochain ((chains R).obj E) J m) (U : Scheme.{0}) (w : ℤ) (p q : ℕ) (y : Sx E p U) (z : Sx E q U) :
    Sec (K.X w) U :=
  if hh : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w then μ.mul U _ _ w hh (ev α p _ rfl U y) (ev β q _ rfl U z) else 0

theorem recombine {G : Type*} [AddCommGroup G] (X Y BF BF' BB BB' : G) (c s K c' P e1 e2 c2 e3 : ℤ) (hF : BF' = BF)
    (hB : BB' = BB) (h2 : c * s = e2 * c2) (h3 : K * c' = c * e1) (h4 : K * (c * P) = e2 * (c2 * e3)) :
    c • (X + s • Y) + K • (c' • BF + c • P • BB) = c • (X + e1 • BF') + e2 • c2 • (Y + e3 • BB') := by
  subst hF hB
  simp only [smul_add, smul_smul]
  rw [h2, h3, h4]
  abel

theorem sign_nat (p : ℕ) : ((-1 : ℤ) ^ p) = (((p : ℤ).negOnePow : ℤˣ) : ℤ) := by
  simp [Int.negOnePow_def]

end LateralTheory.EtaleFoundations.AWLeib

open LateralTheory.EtaleFoundations.AWLeib in

theorem LateralTheory.EtaleFoundations.etaleAlexanderWhitneyCup_leibniz_of_pairing : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupLeibniz := by
  intro R _ I J K μ E n m k hk α β γ γ₁ γ₂ hγ h1 h2
  apply ev_ext
  intro N w hw U x
  rw [ev_add, ev_units_smul, ev_delta_bd rfl γ N (-(N : ℤ) + k) w rfl hw U x, hγ N _ rfl U x, h1 N w hw U x,
    h2 N w hw U x]
  rw [bd_congr (g := fun N' y => ∑ p : Fin (N' + 1), ((m * (p : ℕ)).negOnePow : ℤ) •
      Fm μ α β U w p (N' - p) (y.sub 0 p (by omega)) (y.sub p (N' - p) (by omega))) ?_ x]
  swap
  · intro N' y hN
    rw [dif_pos (by omega), hγ N' w _ U y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Units.smul_def]
    unfold Fm
    rw [dif_pos (by omega)]
  rw [bd_aw (Fm μ α β U w) (fun p : ℕ => ((m * (p : ℤ)).negOnePow : ℤ)) (fun p : ℕ => ((m * ((p : ℤ) - 1)).negOnePow : ℤ))
    (fun p => by congr 2; push_cast; ring) N x]
  rw [secmap_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.2
  rw [Units.smul_def, secmap_zsmul, leib' μ U _ _ _ (-((p : ℕ) : ℤ) + (n + 1)) (-((N - p : ℕ) : ℤ) + (m + 1)) w _ (by ring) (by ring) (by omega)]
  rw [ev_delta_bd rfl α p (-((p : ℕ) : ℤ) + n) _ rfl _ U, ev_delta_bd rfl β (N - p) (-((N - p : ℕ) : ℤ) + m) _ rfl _ U]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, Units.smul_def, mul_bd_left, mul_bd_right]
  refine recombine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · refine bd_congr (fun q z hq => ?_) _
    rw [dif_pos (by omega)]
    unfold Fm
    rw [dif_pos (by omega)]
    exact mul_congr μ U α β _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · refine bd_congr (fun q z hq => ?_) _
    rw [dif_pos (by omega)]
    unfold Fm
    rw [dif_pos (by omega)]
    exact mul_congr μ U α β _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-((p : ℕ) : ℤ), by ring⟩
  · subst hk
    simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by ring⟩
  · subst hk
    rw [sign_nat]
    simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by ring⟩
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCechConerveImageIsoCechNerveOfPreservesWide
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts : Prop :=
  ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ),
    (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V),
    ∃ e : ((Arrow.mk g).cechConerve ⋙ Ψ).leftOp ≅ (Arrow.mk (Ψ.map g).unop).cechNerve,
      lev Ψ (coAug g) = e.hom ≫ (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom

def LateralTheory.EtaleFoundations.CechQuasiIsoOfLocallySurjective : Prop :=
  ∀ (R : Type) [CommRing R] (P Q : PSh) (f : P ⟶ Q), Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f →
    QuasiIso ((chains R).map (Arrow.mk f).augmentedCechNerve.hom)
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalBasicPropertiesHold
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvB
variable {R : Type} [CommRing R]

theorem ev_add {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  simp [ev]

noncomputable def evHom {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p:ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
  AddMonoidHom.mk' (fun α => ev α p s h U x) (fun α β => ev_add α β p s h U x)

theorem ev_compHom {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  simp [ev, Cochain.comp_v _ _ (add_zero n) _ s s h (add_zero s)]

theorem isZero_pos {E : Spc} (a : ℤ) (ha : 0 < a) : IsZero (((chains R).obj E).X a) := by
  apply HomologicalComplex.isZero_extend_X
  intro j hj
  change -(j : ℤ) = a at hj
  omega

theorem free_ext {P : PSh} {F : Shv R} (φ ψ : (free R).obj P ⟶ F)
    (hφ : ∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) : φ = ψ := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ F.cond
  ext U : 2
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have := hφ U.unop x
  simp only [freeGen] at this
  exact this

theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have := congrArg (fun f => ModuleCat.Hom.hom f y) (φ.hom.naturality g.op)
  simpa using this.symm

theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) x :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have key := fun y => congrArg (fun f => ModuleCat.Hom.hom f y)
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  unfold freeGen
  refine ((key _).symm).trans ?_
  congr 1
  simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.whiskeringRight_obj_map, Functor.comp_map, Functor.whiskerRight_app, uliftFunctor_map] <;> try (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  all_goals simp [freeP, ModuleCat.freeMk, ModuleCat.free, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem freeGen_map {P Q : PSh} (f : P ⟶ Q) U x :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have key := fun y => congrArg (fun f => ModuleCat.Hom.hom (NatTrans.app f (op U)) y)
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at key
  unfold freeGen
  refine ((key _).symm).trans ?_
  congr 1
  simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.whiskeringRight_obj_map, Functor.comp_map, Functor.whiskerRight_app, uliftFunctor_map] <;> try (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  all_goals simp [freeP, ModuleCat.freeMk, ModuleCat.free, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem chainsXIso_nat {E' E : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p:ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  simp [chainsXIso, chains, chainsN, HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f p = -(p:ℤ) from rfl)]
  erw [Iso.inv_hom_id_assoc]
  try rfl

theorem ev_res {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  have := sec_nat ((chainsXIso R E p).inv ≫ α.v _ _ h) g (freeGen R _ U x)
  rw [freeGen_res] at this
  exact this

theorem ev_ext {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (hαβ : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β := by
  apply Cochain.ext
  intro a b hab
  by_cases ha : 0 < a
  · exact (isZero_pos a ha).eq_of_src _ _
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = -(k : ℤ) := ⟨(-a).toNat, by omega⟩
  rw [← cancel_epi (chainsXIso R E k).inv]
  exact free_ext _ _ (fun U x => hαβ k b hab U x)

theorem ev_pull {E E' : Spc} {I : Cx R} {n : ℤ} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f) := by
  have e1 : ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)).v (-(p:ℤ)) s h =
      ((chains R).map f).f (-(p:ℤ)) ≫ α.v (-(p:ℤ)) s h := by
    rw [Cochain.comp_v _ _ (zero_add n) (-(p:ℤ)) (-(p:ℤ)) s (add_zero _) h, Cochain.ofHom_v]
  unfold ev
  rw [e1, ← Category.assoc, chainsXIso_nat, Category.assoc]
  have := freeGen_map (R := R) (f.app (op (SimplexCategory.mk p))) U x
  simp only [Sec.map] at this
  simp [this, Sx.map]

end LateralTheory.EtaleFoundations.EvB

theorem LateralTheory.EtaleFoundations.etale_chain_cochain_eval_basic_properties_hold : LateralTheory.EtaleFoundations.EtaleCochainEvaluationLinear := by
  intro R _ E I n
  refine ⟨fun α β p s h U x => ?_, fun α p s h V U g x => LateralTheory.EtaleFoundations.EvB.ev_res α p s h V U g x,
    fun α β hαβ => LateralTheory.EtaleFoundations.EvB.ev_ext α β hαβ, fun f α p s h U x => LateralTheory.EtaleFoundations.EvB.ev_pull f α p s h U x,
    fun m α p s h U x => LateralTheory.EtaleFoundations.EvB.ev_compHom m α p s h U x⟩
  have H := LateralTheory.EtaleFoundations.EvB.evHom (I := I) (n := n) (E := E) p s h U x
  exact ⟨map_add (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) α β, map_sub (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) α β,
    map_zero (LateralTheory.EtaleFoundations.EvB.evHom (I := I) (n := n) p s h U x), fun c => map_zsmul (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) c α⟩
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy : Prop :=
  ∀ (R : Type) [CommRing R] (K L I : Cx R) [I.IsKInjective] (f : K ⟶ L) [QuasiIso f],
    (∀ a : K ⟶ I, ∃ m : L ⟶ I, Nonempty (Homotopy (f ≫ m) a)) ∧
    ∀ m m' : L ⟶ I, Nonempty (Homotopy (f ≫ m) (f ≫ m')) → Nonempty (Homotopy m m')

def LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (I : Cx R) [I.IsStrictlyGE 0] (a b : sgl F ⟶ I),
    Nonempty (Homotopy a b) → a = b

theorem LateralTheory.EtaleFoundations.etale_sheaf_ext_hom_injective_resolution_of_lift_and_rigidity (hA : LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy)
    (hB : LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual) : LateralTheory.EtaleFoundations.EtaleKInjectiveHomExtendsAlongQuasiIso := by
  intro R _ F T I _ _ ε _
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨m, hm⟩ := (hA R (sgl F) T I ε).1 a
    exact ⟨m, hB R F I _ _ hm⟩
  · exact (hA R (sgl F) T I ε).2 m m' ⟨Homotopy.ofEq h⟩
end

