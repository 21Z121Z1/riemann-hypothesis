import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SympBasis

private theorem sum_inv_mulVec_smul_col_of_det_ne_zero {R : Type} [CommRing R] {g : ℕ} (c : Fin (2 * g) → R) (i j : Fin (2 * g))
    (hij : (i : ℕ) < g ∧ (j : ℕ) = i + g) : ∑ l, c l * (Out.stdSymp g l j : R) = c i := by
  rw [Finset.sum_eq_single i]
  · unfold Out.stdSymp
    rw [if_pos hij]
    simp
  · intro l _ hl
    have h1 : ¬ ((l : ℕ) < g ∧ (j : ℕ) = l + g) := fun h => hl (Fin.ext (by omega))
    have h2 : ¬ ((j : ℕ) < g ∧ (l : ℕ) = j + g) := by omega
    unfold Out.stdSymp
    rw [if_neg h1, if_neg h2]
    simp
  · simp

private theorem sum_mul_stdSymp_eq_neg_of_eq_add {R : Type} [CommRing R] {g : ℕ} (c : Fin (2 * g) → R) (i j : Fin (2 * g))
    (hij : (j : ℕ) < g ∧ (i : ℕ) = j + g) : ∑ l, c l * (Out.stdSymp g l j : R) = - c i := by
  rw [Finset.sum_eq_single i]
  · have h1 : ¬ ((i : ℕ) < g ∧ (j : ℕ) = i + g) := by omega
    unfold Out.stdSymp
    rw [if_neg h1, if_pos hij]
    simp
  · intro l _ hl
    have h1 : ¬ ((l : ℕ) < g ∧ (j : ℕ) = l + g) := by omega
    have h2 : ¬ ((j : ℕ) < g ∧ (l : ℕ) = j + g) := fun h => hl (Fin.ext (by omega))
    unfold Out.stdSymp
    rw [if_neg h1, if_neg h2]
    simp
  · simp

theorem eq_of_sum_stdSymp {R : Type} [CommRing R] {g : ℕ} (a b : Fin (2 * g) → R)
    (h : ∀ j, ∑ i, a i * (Out.stdSymp g i j : R) = ∑ i, b i * (Out.stdSymp g i j : R)) : a = b := by
  funext i
  have hi2 := i.isLt
  by_cases hi : (i : ℕ) < g
  ·
    have h1 := h ⟨i + g, by omega⟩
    rwa [sum_inv_mulVec_smul_col_of_det_ne_zero a i _ ⟨hi, rfl⟩, sum_inv_mulVec_smul_col_of_det_ne_zero b i _ ⟨hi, rfl⟩] at h1
  ·
    have h1 := h ⟨i - g, by omega⟩
    rw [sum_mul_stdSymp_eq_neg_of_eq_add a i _ ⟨by simp; omega, by simp; omega⟩,
      sum_mul_stdSymp_eq_neg_of_eq_add b i _ ⟨by simp; omega, by simp; omega⟩] at h1
    exact neg_inj.mp h1

theorem rel_prod {M U : Type} [CommMonoid M] [CommGroup U] (W : M → U → Prop) (h1 : W 1 1)
    (hm : ∀ x x' c c', W x c → W x' c' → W (x * x') (c * c')) {J : Type} (s : Finset J) (p : J → M) (u : J → U)
    (a : J → ℕ) (hp : ∀ i, W (p i) (u i)) : W (∏ i ∈ s, p i ^ a i) (∏ i ∈ s, u i ^ a i) := by
  classical
  have hpow : ∀ i (n : ℕ), W (p i ^ n) (u i ^ n) := by
    intro i n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact hm _ _ _ _ ih (hp i)
  refine Finset.induction_on s (by simpa using h1) ?_
  intro j t hj ih
  rw [Finset.prod_insert hj, Finset.prod_insert hj]
  exact hm _ _ _ _ (hpow j (a j)) ih

private theorem zpow_finset_sum_divisor {U : Type} [CommGroup U] (z : U) {I : Type} (s : Finset I) (f : I → ℤ) :
    z ^ (∑ i ∈ s, f i) = ∏ i ∈ s, z ^ f i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro j t hj ih
  rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem injective_of_pairing {M U : Type} [CommMonoid M] [CommGroup U] (W : M → M → U → Prop) (k : ℕ) [NeZero k]
    (hu : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) {g : ℕ} (p : Fin (2 * g) → M)
    (hp : ∀ i, p i ^ k = 1) (z : U) (hz : IsPrimitiveRoot z k)
    (hw : ∀ i j, W (p i) (p j) (z ^ Out.stdSymp g i j)) :
    Function.Injective fun c : Fin (2 * g) → ZMod k => ∏ i, p i ^ (c i).val := by
  classical

  have hone : ∀ y, y ^ k = 1 → W 1 y 1 := by
    intro y hy
    obtain ⟨c, hc, huniq⟩ := hu 1 y (one_pow k) hy
    have h2 : W 1 y (c * c) := by simpa using hm 1 1 y c c hc hc
    have hcc : c * c = c := huniq _ h2
    have hc1 : c = 1 := by simpa using hcc
    rw [hc1] at hc
    exact hc

  let e : (Fin (2 * g) → ZMod k) → Fin (2 * g) → ℤ := fun c j => ∑ i, Out.stdSymp g i j * ((c i).val : ℤ)
  have hW : ∀ (c : Fin (2 * g) → ZMod k) j, W (∏ i, p i ^ (c i).val) (p j) (z ^ e c j) := by
    intro c j
    have h := rel_prod (fun x v => W x (p j) v) (hone _ (hp j))
      (fun x x' v v' hx hx' => hm x x' (p j) v v' hx hx') Finset.univ p
      (fun i => z ^ Out.stdSymp g i j) (fun i => (c i).val) (fun i => hw i j)
    have hz' : (∏ i, (z ^ Out.stdSymp g i j) ^ (c i).val) = z ^ e c j := by
      simp only [e, zpow_finset_sum_divisor]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_natCast, ← zpow_mul]
    simpa only [hz'] using h
  have htors : ∀ c : Fin (2 * g) → ZMod k, (∏ i, p i ^ (c i).val) ^ k = 1 := by
    intro c
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, hp i, one_pow]
  intro c c' hcc
  have hcc' : (∏ i, p i ^ (c i).val) = ∏ i, p i ^ (c' i).val := hcc
  have key : ∀ j, z ^ e c j = z ^ e c' j := by
    intro j
    obtain ⟨w, _, huniq⟩ := hu _ (p j) (htors c) (hp j)
    have h1 := huniq _ (hW c j)
    have h2 := huniq _ (hcc' ▸ hW c' j)
    rw [h1, h2]
  apply eq_of_sum_stdSymp (R := ZMod k) c c'
  intro j
  have hd : ((e c j : ℤ) : ZMod k) = ((e c' j : ℤ) : ZMod k) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ← hz.zpow_eq_one_iff_dvd, zpow_sub, key j, mul_inv_cancel]
  simpa [e, mul_comm] using hd

private theorem comp_list_prod_eq_prod_map_comp_over {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T)
    (l : List (T ⟶ A)) : f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp [MonObj.comp_one]
  | cons x l ih => simp [List.prod_cons, MonObj.comp_mul, ih]

theorem comp_linComb {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (a : Fin n → ℕ) : f ≫ Out.linComb y a = Out.linComb (fun i => f ≫ y i) a := by
  unfold Out.linComb
  rw [comp_list_prod_eq_prod_map_comp_over, List.map_ofFn]
  simp [Function.comp_def, MonObj.comp_pow]

end GlobalTheory.SympBasis

namespace GlobalTheory

open SympBasis in

theorem symplectic_system_torsion_basis :
    Out.Laws → ∀ (K₀ : Type) [Field K₀] (P : Out.PolAV (Sp K₀)) (k : ℕ) (ze : K₀ˣ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K₀) ⟶ P.A)), (k : K₀) ≠ 0 → IsPrimitiveRoot ze k → (∀ i, pt i ^ k = 1) → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn ze ^ Out.stdSymp P.g i j)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp K₀) (y : Over.mk x ⟶ P.A), y ^ k = 1 → ∃! c : Fin (2 * P.g) → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K₀)) ≫ pt i) (fun i => (c i).val) = y := by
  intro hL K₀ _ P k ze pt hk hze hpt hw K _ _ x y hy
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk (by simp)
  have : NeZero k := ⟨hk0⟩
  have hsep : IsSeparated P.A.hom := by
    obtain ⟨_, _, _, _⟩ := P.isAb
    infer_instance

  let h : Over.mk x ⟶ Out.baseOver (Sp K₀) := Over.homMk x (by simp)

  have hpre : ∀ s s' : Out.baseOver (Sp K₀) ⟶ P.A, h ≫ s = h ≫ s' → s = s' := by
    intro s s' hss
    have : IsReduced (Out.baseOver (Sp K₀)).left := inferInstanceAs (IsReduced (Sp K₀))
    have : IsDominant (X := Sp K) (Y := (Out.baseOver (Sp K₀)).left) x :=
      inferInstanceAs (IsDominant (X := Sp K) (Y := Sp K₀) x)
    apply Over.OverMorphism.ext
    refine ext_of_isDominant_of_isSeparated P.A.hom ?_ x ?_
    · rw [Over.w s, Over.w s']
    · simpa [h] using congrArg CommaMorphism.left hss

  have hzu : IsPrimitiveRoot (unitOn ze) k := by
    unfold unitOn
    refine hze.map_of_injective (Units.map_injective ?_)
    exact Function.LeftInverse.injective
      (g := (Scheme.ΓSpecIso (CommRingCat.of K₀)).hom.hom) fun a => by simp

  obtain ⟨hu, hm, -, -⟩ := hL.weil (Sp K₀) P k (Out.baseOver (Sp K₀))
  have hinj0 := SympBasis.injective_of_pairing (fun a b c => Out.WeilIs P.A P.L (k : ℤ) a b c) k hu
    (fun a a' b c c' => hm a a' b c c') pt hpt (unitOn ze) hzu hw

  have hlin : ∀ c : Fin (2 * P.g) → ZMod k,
      Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val) = h ≫ ∏ i, pt i ^ (c i).val := by
    intro c
    rw [← SympBasis.comp_linComb]
    unfold Out.linComb
    rw [List.prod_ofFn]
  have htors : ∀ c : Fin (2 * P.g) → ZMod k,
      (Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val)) ^ k = 1 := by
    intro c
    rw [hlin, ← MonObj.comp_pow, ← Finset.prod_pow,
      Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hpt i, one_pow]]
    exact MonObj.comp_one _
  let Φ : (Fin (2 * P.g) → ZMod k) → {y : Over.mk x ⟶ P.A // y ^ k = 1} := fun c => ⟨_, htors c⟩
  have hΦ : Function.Injective Φ := by
    intro c c' hcc
    have h1 : Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val) =
        Out.linComb (fun i => h ≫ pt i) (fun i => (c' i).val) := congrArg Subtype.val hcc
    rw [hlin, hlin] at h1
    exact hinj0 (hpre _ _ h1)

  have hkK : ((k : ℕ) : K) ≠ 0 := by
    have hc : ((k : ℕ) : K) = (Spec.preimage x).hom (k : K₀) := by simp
    rw [hc]
    exact (map_ne_zero_iff _ (Spec.preimage x).hom.injective).2 hk
  have hcard := (hL.mulN (Sp K₀) P k (Nat.one_le_iff_ne_zero.2 hk0)).2.2.2.2 K x hkK
  have : Finite {y : Over.mk x ⟶ P.A // y ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hbij : Function.Bijective Φ := hΦ.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin])
  obtain ⟨c, hc⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨c, congrArg Subtype.val hc,
    fun c' hc' => hbij.1 (Subtype.ext (hc'.trans (congrArg Subtype.val hc).symm))⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsometryOfFiniteLevelIsometries
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TateTower

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def LevelIso (D : Datum H) {K : Type} [Field K] {Q : Type} [Group Q] (act : 𝓞 E → Q → Q)
    (e : ℕ → Q → Q → Kˣ → Prop) (N : ℕ) (p : Kˣ × (D.La → Q)) : Prop :=
  IsPrimitiveRoot p.1 N ∧ (∀ a c, p.2 (a + c) = p.2 a * p.2 c) ∧ (∀ (c : 𝓞 E) a, p.2 (c • a) = act c (p.2 a)) ∧
    (∀ a, p.2 a = 1 ↔ ∃ c, a = N • c) ∧ (∀ x, x ^ N = 1 ↔ ∃ a, p.2 a = x) ∧
    ∀ a c, e N (p.2 a) (p.2 c) (p.1 ^ D.EF a c)

variable {D : Datum H} {K : Type} [Field K] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem map_nsmul_of_add {M : Type} [AddCommGroup M] {f : M → Q} (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : M) : f (n • a) = f a ^ n :=
  map_nsmul (AddMonoidHom.mk' (fun a => Additive.ofMul (f a)) hf) n a

theorem nsmul_cancel (D : Datum H) {r : ℕ} (hr : 0 < r) {a c : D.La} (h : r • a = r • c) : a = c := by
  have := D.proj
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have h' : (r : ℤ) • a = (r : ℤ) • c := by simpa only [natCast_zsmul] using h
  exact smul_right_injective D.La (by exact_mod_cast hr.ne' : (r : ℤ) ≠ 0) h'

theorem LevelIso.pow
    (he : ∀ n m x x' c, 0 < n → 0 < m → x ^ (n * m) = 1 → x' ^ (n * m) = 1 → e (n * m) x x' c →
      e n (x ^ m) (x' ^ m) (c ^ m))
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) {p : Kˣ × (D.La → Q)} (h : LevelIso D act e (N * r) p) :
    LevelIso D act e N (p ^ r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hp : ∀ a, (p ^ r).2 a = p.2 (r • a) := fun a => (map_nsmul_of_add h2 r a).symm
  refine ⟨h1.pow (Nat.mul_pos hN hr) (mul_comm _ _), fun a c => ?_, fun c a => ?_, fun a => ?_, fun x => ?_,
    fun a c => ?_⟩
  · rw [hp, hp, hp, smul_add, h2]
  · rw [hp, hp, smul_comm, h3]
  · rw [hp, h4]
    refine exists_congr fun c => ⟨fun h => nsmul_cancel D hr ?_, fun h => ?_⟩
    · rw [h, mul_comm, mul_smul]
    · rw [h, mul_comm, mul_smul]
  · constructor
    · intro hx
      obtain ⟨a, rfl⟩ := (h5 x).1 (by rw [pow_mul, hx, one_pow])
      rw [← map_nsmul_of_add h2, h4] at hx
      obtain ⟨c, hc⟩ := hx
      rw [mul_smul] at hc
      exact ⟨c, by rw [hp, nsmul_cancel D hN hc]⟩
    · rintro ⟨a, rfl⟩
      rw [hp, ← map_nsmul_of_add h2, h4]
      exact ⟨a, by rw [mul_smul]⟩
  · have := he N r _ _ _ hN hr ((h5 _).2 ⟨a, rfl⟩) ((h5 _).2 ⟨c, rfl⟩) (h6 a c)
    have e1 : (p.1 ^ D.EF a c) ^ r = (p.1 ^ r) ^ D.EF a c := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [e1] at this
    exact this

theorem finite_levelIso {N : ℕ} (hN : 0 < N) (hQ : Finite {x : Q // x ^ N = 1}) :
    {p | LevelIso D act e N p}.Finite := by
  have := D.fin
  have hf : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  obtain ⟨S, hS, hSf⟩ := AddGroup.fg_iff.1 (Module.Finite.iff_addGroup_fg.1 hf)
  have := hSf.to_subtype
  have hQ' : {x : Q | x ^ N = 1}.Finite := hQ
  have hζ : {ζ : Kˣ | ζ ^ N = 1}.Finite := by
    have : NeZero N := ⟨hN.ne'⟩
    have : Finite (rootsOfUnity N K) := inferInstance
    exact this
  refine Set.Finite.of_finite_image (f := fun p => (p.1, fun s : S => p.2 s))
    ((hζ.prod (Set.Finite.pi' (fun _ : S => hQ'))).subset ?_) ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨hp.1.pow_eq_one, fun s => (hp.2.2.2.2.1 _).2 ⟨_, rfl⟩⟩
  · intro p hp q hq h
    refine Prod.ext (Prod.ext_iff.1 h).1 (funext fun a => ?_)
    have := AddMonoidHom.eq_of_eqOn_dense hS
      (f := AddMonoidHom.mk' (fun a => Additive.ofMul (p.2 a)) hp.2.1)
      (g := AddMonoidHom.mk' (fun a => Additive.ofMul (q.2 a)) hq.2.1)
      (fun s hs => congrFun (Prod.ext_iff.1 h).2 ⟨s, hs⟩)
    exact DFunLike.congr_fun this a

theorem tateIso_of_levels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (k : ℕ) (z : K) (κ : Type) (lam : κ → D.La) (y : κ → Q), 0 < k → (∀ n, 0 < n → Finite {x : Q // x ^ n = 1}) → (∀ n m x x' c, 0 < n → 0 < m → x ^ (n * m) = 1 → x' ^ (n * m) = 1 → e (n * m) x x' c → e n (x ^ m) (x' ^ m) (c ^ m)) → (∀ m, 0 < m → ∃ (ζ : Kˣ) (ev : D.La → Q), IsPrimitiveRoot ζ (k * m) ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = act c (ev a)) ∧ (∀ a, ev a = 1 ↔ ∃ c, a = (k * m) • c) ∧ (∀ x, x ^ (k * m) = 1 ↔ ∃ a, ev a = x) ∧ (∀ a c, e (k * m) (ev a) (ev c) (ζ ^ D.EF a c)) ∧ (ζ : K) ^ m = z ∧ ∀ i, ev (lam i) ^ m = y i) → ∃ I : TateIso D K Q act e, (I.ζ k : K) = z ∧ ∀ i, I.ev k (lam i) = y i := by
  intro E _ _ _ H D K _ Q _ act e k z κ lam y hk hQ he hex
  have hx : ∀ j : ℕ, ∃ p : Kˣ × (D.La → Q), LevelIso D act e (k * j.factorial) p ∧
      (p.1 : K) ^ j.factorial = z ∧ ∀ i, p.2 (lam i) ^ j.factorial = y i := fun j => by
    obtain ⟨ζ, ev, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hex _ j.factorial_pos
    exact ⟨(ζ, ev), ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
  choose x hx hz hy using hx
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : ∀ n, 0 < n → ∀ᶠ j : ℕ in U, n ∣ k * j.factorial := fun n hn =>
    Ultrafilter.of_le _ ((Filter.eventually_ge_atTop n).mono fun j hj =>
      Dvd.dvd.mul_left (Nat.dvd_factorial hn hj) k)
  have hs : ∀ n, 0 < n → ∃ s, LevelIso D act e n s ∧ ∀ᶠ j in U, x j ^ (k * j.factorial / n) = s := fun n hn => by
    have hm : {p | LevelIso D act e n p} ∈ U.map fun j => x j ^ (k * j.factorial / n) := by
      refine (hU n hn).mono fun j hj => ?_
      have hj' := hx j
      have hpos := Nat.mul_pos hk j.factorial_pos
      rw [← Nat.mul_div_cancel' hj] at hj'
      exact hj'.pow he hn (Nat.div_pos (Nat.le_of_dvd hpos hj) hn)
    obtain ⟨s, h1, h2⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_levelIso hn (hQ n hn)) hm
    refine ⟨s, h1, ?_⟩
    have : {s} ∈ U.map fun j => x j ^ (k * j.factorial / n) := by
      rw [h2]
      exact rfl
    exact this
  have hs' : ∀ n, ∃ s, LevelIso D act e (max n 1) s ∧ ∀ᶠ j in U, x j ^ (k * j.factorial / max n 1) = s :=
    fun n => hs _ (by omega)
  choose s hs1 hs2 using hs'
  have hs3 : ∀ n, 0 < n → LevelIso D act e n (s n) := fun n hn => by
    have := hs1 n
    rwa [max_eq_left hn] at this
  have hs4 : ∀ n, 0 < n → ∀ᶠ j in U, x j ^ (k * j.factorial / n) = s n := fun n hn => by
    have := hs2 n
    rwa [max_eq_left hn] at this
  have htow : ∀ n m, 0 < n → 0 < m → s (n * m) ^ m = s n := fun n m hn hm => by
    have hnm := Nat.mul_pos hn hm
    obtain ⟨j, h1, h2, c, h3⟩ := ((hs4 _ hnm).and ((hs4 n hn).and (hU _ hnm))).exists
    rw [← h1, ← h2, h3, ← pow_mul, Nat.mul_div_cancel_left _ hnm, Nat.mul_assoc, Nat.mul_div_cancel_left _ hn,
      mul_comm c m]
  obtain ⟨j, hj⟩ := (hs4 k hk).exists
  rw [Nat.mul_div_cancel_left _ hk] at hj
  refine ⟨⟨fun n => (s n).1, fun n hn => (hs3 n hn).1, fun n m hn hm => congrArg Prod.fst (htow n m hn hm),
    fun n => (s n).2, fun n => (hs1 n).2.1, fun n => (hs1 n).2.2.1, fun n hn => (hs3 n hn).2.2.2.1,
    fun n hn => (hs3 n hn).2.2.2.2.1, fun n m hn hm a => congrFun (congrArg Prod.snd (htow n m hn hm)) a,
    fun n hn => (hs3 n hn).2.2.2.2.2⟩, ?_, fun i => ?_⟩
  · show ((s k).1 : K) = z
    rw [← hj, ← hz j]
    exact Units.val_pow_eq_pow_val _ _
  · show (s k).2 (lam i) = y i
    rw [← hj, ← hy j i]
    rfl

end GlobalTheory.TateTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsometryPrimitiveRootBijectiveModN
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsIsometry

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.TorsIsometry.exists_eq_nsmul_of_dvd {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)
    (hB : Function.Bijective B) (n : ℕ) (d : M) (hd : ∀ b, (n : ℤ) ∣ B d b) : ∃ f : M, d = n • f := by
  let φ : M →ₗ[ℤ] ℤ :=
    { toFun := fun b => B d b / n
      map_add' := fun x y => by
        simp only [map_add]
        exact Int.add_ediv_of_dvd_left (hd x)
      map_smul' := fun c x => by
        simp only [map_zsmul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hd x) }
  obtain ⟨f, hf⟩ := hB.2 φ
  refine ⟨f, hB.1 ?_⟩
  ext b
  simp only [map_nsmul, LinearMap.smul_apply, hf, nsmul_eq_mul]
  exact (Int.mul_ediv_cancel' (hd b)).symm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.TorsIsometry.ker_and_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (e : Q → Q → Kˣ → Prop) (n : ℕ) (ζ : Kˣ) (ev : D.La → Q), 0 < n → Nat.card {y : Q // y ^ n = 1} = n ^ Module.finrank ℤ D.La → (∀ y c, y ^ n = 1 → e 1 y c → c = 1) → IsPrimitiveRoot ζ n → (∀ a c, ev (a + c) = ev a * ev c) → (∀ a, ev a ^ n = 1) → (∀ a c, e (ev a) (ev c) (ζ ^ D.EF a c)) → (∀ a, ev a = 1 ↔ ∃ c, a = n • c) ∧ ∀ y, y ^ n = 1 ↔ ∃ a, ev a = y := by
  intro E _ _ _ H D K _ Q _ e n ζ ev hn hcard he1 hζ hev hevn hpair
  have hev0 : ev 0 = 1 := by
    have h := hev 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hevsmul : ∀ (m : ℕ) (c : D.La), ev (m • c) = ev c ^ m := by
    intro m c
    induction m with
    | zero => simp [hev0]
    | succ m ih => rw [succ_nsmul, hev, ih, pow_succ]
  have hker : ∀ a, ev a = 1 ↔ ∃ c, a = n • c := by
    intro a
    constructor
    · intro ha
      refine _root_.GlobalTheory.TorsIsometry.exists_eq_nsmul_of_dvd D.EF D.unimod n a fun c => ?_
      have h := hpair a c
      rw [ha] at h
      exact (hζ.zpow_eq_one_iff_dvd _).1 (he1 _ _ (hevn c) h)
    · rintro ⟨c, rfl⟩
      rw [hevsmul, hevn]
  refine ⟨hker, fun y => ⟨fun hy => ?_, ?_⟩⟩
  swap
  · rintro ⟨a, rfl⟩
    exact hevn a
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI := D.fin
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : NoZeroSMulDivisors ℤ D.La := ⟨fun {c x} h => by
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      apply D.unimod.1
      ext b
      have := congrArg (fun x => D.EF x b) h
      simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, map_zero,
        LinearMap.zero_apply] at this
      simpa [hc] using this⟩
  haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ D.La
  let g : (Fin (Module.finrank ℤ D.La) → ZMod n) → {y : Q // y ^ n = 1} :=
    fun t => ⟨ev (b.equivFun.symm fun i => ((t i).val : ℤ)), hevn _⟩
  have hinj : Function.Injective g := by
    intro t t' htt
    have h : ev (b.equivFun.symm fun i => ((t i).val : ℤ)) =
        ev (b.equivFun.symm fun i => ((t' i).val : ℤ)) := congrArg Subtype.val htt
    have hdiff : ev ((b.equivFun.symm fun i => ((t i).val : ℤ)) -
        b.equivFun.symm fun i => ((t' i).val : ℤ)) = 1 := by
      have h2 := hev ((b.equivFun.symm fun i => ((t i).val : ℤ)) -
        b.equivFun.symm fun i => ((t' i).val : ℤ)) (b.equivFun.symm fun i => ((t' i).val : ℤ))
      rw [sub_add_cancel, h] at h2
      exact mul_eq_right.1 h2.symm
    obtain ⟨c, hc⟩ := (hker _).1 hdiff
    funext i
    have hi := congrArg (fun z => b.equivFun z i) hc
    simp only [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply, map_nsmul,
      Pi.smul_apply, nsmul_eq_mul] at hi
    have hcast := congrArg (Int.cast : ℤ → ZMod n) hi
    push_cast at hcast
    simpa [sub_eq_zero] using hcast
  haveI : Finite {y : Q // y ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hbij : Function.Bijective g := hinj.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_fun, Nat.card_zmod, Nat.card_fin])
  obtain ⟨t, ht⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨_, congrArg Subtype.val ht⟩

end GlobalTheory.TorsIsometry
end

