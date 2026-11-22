import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0125
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0121
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixFrobenius
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie.MatF

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.φD_smulA (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (a : _root_.Formalism.BasicNotions.LetA O n)
    (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.γD_smulA (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (g : W.Gam) (a : _root_.Formalism.BasicNotions.LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in

theorem _root_.GlobalTheory.WachTie.MatF.coord_unique (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) (c d : Fin r → _root_.Formalism.BasicNotions.LetA O n)
    (h : ∑ m, c m • (b m : W.DD T) = ∑ m, d m • (b m : W.DD T)) : c = d := by
  have h' : ∑ m, c m • b m = ∑ m, d m • b m := Subtype.ext (by simpa [Submodule.coe_sum] using h)
  exact b.equivFun.symm.injective (by rw [b.equivFun_symm_apply, b.equivFun_symm_apply]; exact h')

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.exists_coord (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) (x : W.DD T) (hx : x ∈ W.N T) :
    ∃ c : Fin r → _root_.Formalism.BasicNotions.LetA O n, x = ∑ m, c m • (b m : W.DD T) := by
  refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
  have h := congrArg Subtype.val (b.sum_equivFun ⟨x, hx⟩)
  rw [Submodule.coe_sum] at h
  simpa only [Submodule.coe_smul] using h.symm

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.exists_matrix_frobenius (R : _root_.GlobalTheory.NB.Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) (hF : _root_.GlobalTheory.WachTie.FrTie W R j)
    (_hE : _root_.GlobalTheory.WachTie.EETie W R j jE)
    (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (hs : W.s = 1) (hu : IsUnit (W.DelF.card : O)) :
    ∃ (M : ℕ) (Φ : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧),
      (∀ i, ∃ (k : ℕ) (Ψ : Matrix (Fin r) (Fin r) O⟦X⟧),
        Φ i * Ψ = R.E ^ k • (1 : Matrix (Fin r) (Fin r) O⟦X⟧)) ∧
      (∀ k, (fun _ => j R.E : _root_.Formalism.BasicNotions.LetA O n) ^ M • W.φD T (b k : W.DD T) =
        ∑ m, (fun i => j (Φ i m k) : _root_.Formalism.BasicNotions.LetA O n) • (b m : W.DD T)) := by
  classical
  obtain ⟨hj, hrange, -, -, -, -, -, u, hu'⟩ := hF
  set q : _root_.Formalism.BasicNotions.LetA O n := fun _ => W.q₀ with hq
  set e : _root_.Formalism.BasicNotions.LetA O n := fun _ => j R.E with he
  set w : _root_.Formalism.BasicNotions.LetA O n := fun _ => ((u⁻¹ : O⟦X⟧ˣ) : O⟦X⟧) with hw
  have hqe : e = w * q := by
    funext i
    simp only [he, hw, hq, Pi.mul_apply]
    rw [← hu', mul_left_comm, Units.inv_mul, mul_one]
  have hpow : ∀ k (x : W.DD T), ((_root_.Formalism.BasicNotions.letφ (n := n) W.φ₀ ^ (W.s - 1)) fun _ => W.q₀) ^ k • x = q ^ k • x := by
    intro k x
    rw [hs, Nat.sub_self, pow_zero]
    rfl
  have hinv : ∀ y : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ y = y) → j (Function.invFun j y) = y :=
    fun y hy => Function.invFun_eq ((hrange y).2 hy)
  have hγe : ∀ δ ∈ W.DelF, W.γA δ e = e := by
    intro δ hδ
    funext i
    exact (hrange _).1 ⟨_, rfl⟩ δ hδ
  have hbN : ∀ k, (b k : W.DD T) ∈ W.N T := fun k => (b k).2
  have hbΔ : ∀ k, ∀ δ ∈ W.DelF, W.γD T δ (b k) = b k := fun k => (hb k).2
  have hlift : ∀ (f : Fin r → ℕ) (k : Fin r) (x : W.DD T), q ^ f k • x ∈ W.N T →
      e ^ (∑ m, f m) • x ∈ W.N T := by
    intro f k x hx
    have h1 := (W.N T).smul_mem (w ^ (∑ m, f m) * q ^ (∑ m, f m - f k)) hx
    rwa [smul_smul, mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)),
      ← mul_pow, ← hqe] at h1
  choose nφ hnφ using fun k => W.N_φ T _ (hbN k)
  have hyN : ∀ k, e ^ (∑ m, nφ m) • W.φD T (b k) ∈ W.N T := fun k =>
    hlift nφ k _ (by rw [← hpow]; exact hnφ k)
  set M := ∑ m, nφ m with hM
  choose C hC using fun k => _root_.GlobalTheory.WachTie.MatF.exists_coord W T b _ (hyN k)
  have hCinv : ∀ k m, ∀ δ ∈ W.DelF, W.γA δ (C k m) = C k m := by
    intro k m δ hδ
    have h := congrArg (W.γD T δ) (hC k)
    rw [_root_.GlobalTheory.WachTie.MatF.γD_smulA, map_pow, hγe δ hδ, ← W.φγ_comm, hbΔ k δ hδ, hC k, map_sum] at h
    simp only [_root_.GlobalTheory.WachTie.MatF.γD_smulA, hbΔ _ δ hδ] at h
    exact congrFun (_root_.GlobalTheory.WachTie.MatF.coord_unique W T b _ _ h.symm) m

  choose kk hkk using fun m => W.N_φinv T _ (hbN m)
  have hspan : Submodule.span (_root_.Formalism.BasicNotions.LetA O n) (W.φD T '' W.N T) ≤
      Submodule.span (_root_.Formalism.BasicNotions.LetA O n) (Set.range fun t => W.φD T (b t)) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := _root_.GlobalTheory.WachTie.MatF.exists_coord W T b y hy
    rw [map_sum]
    refine Submodule.sum_mem _ fun t _ => ?_
    rw [_root_.GlobalTheory.WachTie.MatF.φD_smulA]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  have hA : ∀ m, ∃ a : Fin r → _root_.Formalism.BasicNotions.LetA O n,
      ∑ t, a t • W.φD T (b t) = e ^ (∑ m', kk m') • (b m : W.DD T) := by
    intro m
    rw [← Submodule.mem_span_range_iff_exists_fun]
    apply hspan
    have h1 := (Submodule.span (_root_.Formalism.BasicNotions.LetA O n) (W.φD T '' W.N T)).smul_mem
      (w ^ (∑ m', kk m') * q ^ (∑ m', kk m' - kk m)) (hkk m)
    rw [hpow] at h1
    rwa [smul_smul, mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)),
      ← mul_pow, ← hqe] at h1
  choose a ha using hA
  set K := ∑ m', kk m' with hK
  set c := e ^ (M + K) with hc
  set P : Matrix (Fin r) (Fin r) (_root_.Formalism.BasicNotions.LetA O n) := Matrix.of fun m k => C k m with hP
  set A : Matrix (Fin r) (Fin r) (_root_.Formalism.BasicNotions.LetA O n) := Matrix.of fun t m => a m t with hAdef
  have hPA : P * A = c • 1 := by
    refine Matrix.ext fun m' m => ?_
    have h : ∑ m'', (∑ t, a m t * C t m'') • (b m'' : W.DD T) =
        ∑ m'', (Pi.single m c : Fin r → _root_.Formalism.BasicNotions.LetA O n) m'' • (b m'' : W.DD T) := by
      simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hc, pow_add, mul_smul, ← ha m, Finset.smul_sum]
      simp_rw [smul_comm (e ^ M) (a m _), hC, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h2 := congrFun (_root_.GlobalTheory.WachTie.MatF.coord_unique W T b _ _ h) m'
    simp only [Matrix.mul_apply, hP, hAdef, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [Finset.sum_congr rfl fun t _ => mul_comm _ _, h2, Pi.single_apply]
    split_ifs <;> simp

  have hγP : ∀ δ ∈ W.DelF, P.map (W.γA δ) = P := by
    intro δ hδ
    refine Matrix.ext fun m k => ?_
    exact hCinv k m δ hδ
  have hγc : ∀ δ ∈ W.DelF, W.γA δ c = c := by
    intro δ hδ
    rw [hc, map_pow, hγe δ hδ]
  have hdet : P.det * A.det = c ^ r := by
    rw [← Matrix.det_mul, hPA, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hγdetP : ∀ δ ∈ W.DelF, W.γA δ P.det = P.det := by
    intro δ hδ
    have h := RingHom.map_det (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n) P
    rw [show (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n).mapMatrix P = P from hγP δ hδ] at h
    exact h
  have hγadj : ∀ δ ∈ W.DelF, ∀ x y, W.γA δ (P.adjugate x y) = P.adjugate x y := by
    intro δ hδ x y
    have h := RingHom.map_adjugate (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n) P
    rw [show (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n).mapMatrix P = P from hγP δ hδ] at h
    exact congrFun (congrFun h x) y
  set v := c ^ r * A.det with hv
  have hγv : ∀ δ ∈ W.DelF, W.γA δ v = v := by
    intro δ hδ
    have h1 : P.det * W.γA δ A.det = P.det * A.det := by
      rw [hdet, ← hγdetP δ hδ, ← map_mul, hdet, map_pow, hγc δ hδ]
    rw [hv, map_mul, map_pow, hγc δ hδ]
    calc c ^ r * W.γA δ A.det = A.det * (P.det * W.γA δ A.det) := by rw [← hdet]; ring
      _ = c ^ r * A.det := by rw [h1, ← hdet]; ring
  set Ψf := v • P.adjugate with hΨf
  have hPΨ : P * Ψf = c ^ (r + r) • 1 := by
    rw [hΨf, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, pow_add, hv, ← hdet]
    congr 1
    ring
  have hγΨ : ∀ δ ∈ W.DelF, ∀ x y, W.γA δ (Ψf x y) = Ψf x y := by
    intro δ hδ x y
    rw [hΨf, Matrix.smul_apply, smul_eq_mul, map_mul, hγv δ hδ, hγadj δ hδ]
  have hjP : ∀ i m k, j (Function.invFun j (P m k i)) = P m k i := fun i m k =>
    hinv _ fun δ hδ => congrFun (hCinv k m δ hδ) i
  have hjΨ : ∀ i x y, j (Function.invFun j (Ψf x y i)) = Ψf x y i := fun i x y =>
    hinv _ fun δ hδ => congrFun (hγΨ δ hδ x y) i
  refine ⟨M, fun i => Matrix.of fun m k => Function.invFun j (P m k i), fun i =>
    ⟨(M + K) * (r + r), Matrix.of fun x y => Function.invFun j (Ψf x y i), ?_⟩, fun k => ?_⟩
  · refine Matrix.ext fun x y => ?_
    apply hj
    have h := congrFun (congrFun (congrFun hPΨ x) y) i
    simp only [Matrix.mul_apply, Finset.sum_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Pi.mul_apply] at h
    simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, hjP, hjΨ, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    rw [h]
    split_ifs <;> simp [hc, he, pow_mul]
  · rw [hC k]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    funext i
    exact (hjP i m k).symm

end GlobalTheory.WachTie.MatF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableQuadraticGaussIntegral
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.GaussStable

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem NL_add [Unram F E] (A : Et F E) (y m : A.L) :
    A.NL (y + m) = A.NL y + Algebra.trace A.K A.L (star m * y) + A.NL m := by
  obtain ⟨-, hinj, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  apply hinj
  rw [map_add, map_add, hN, hN, hN, htr, star_add, star_mul, star_star]
  ring

theorem NL_zero [Unram F E] (A : Et F E) : A.NL 0 = 0 := by
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  apply hinj
  rw [hN, zero_mul, map_zero]

theorem formL_symm_nondeg [U : Unram F E] (A : Et F E) (v : A.Kˣ) :
    (EtMeas.formL A v).IsSymm ∧ (EtMeas.formL A v).Nondegenerate := by
  have := U.charZero
  have := EtMeas.finite_L A
  obtain ⟨-, hinj, -, htr, hnd⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have hs : (EtMeas.formL A v).IsSymm := ⟨fun y y' => by
    rw [EtMeas.formL_apply, EtMeas.formL_apply]
    congr 2
    apply hinj
    rw [htr, htr]; simp [add_comm, mul_comm]⟩
  have hl : ∀ y', (∀ y, EtMeas.formL A v y' y = 0) → y' = 0 := fun y' h => hnd y' fun y => by
    have h1 : (v : A.K) * Algebra.trace A.K A.L (star y' * y) = 0 := EtMeas.eq_zero_of_trace F A.K _ fun k => by
      have := h (k • y)
      rw [EtMeas.formL_apply, mul_smul_comm, map_smul, smul_eq_mul] at this
      rw [← this]; congr 1; ring
    simpa using h1
  exact ⟨hs, ⟨hl, fun y h => hl y fun y' => by rw [hs.eq]; exact h y'⟩⟩

open Classical in

theorem integral_indicator_char {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (M : AddSubgroup V)
    (hMo : IsOpen (M : Set V)) (χ : V → ℂ) (hχ : ∀ a b, χ (a + b) = χ a * χ b) :
    ∫ m, (M : Set V).indicator χ m ∂μ = if ∀ m ∈ M, χ m = 1 then (μ.real (M : Set V) : ℂ) else 0 := by
  classical
  split_ifs with h
  · rw [show (M : Set V).indicator χ = (M : Set V).indicator (fun _ => (1 : ℂ)) from
      Set.indicator_congr (fun m hm => h m hm), integral_indicator_const _ hMo.measurableSet]
    simp
  · push Not at h
    obtain ⟨m0, hm0, h1⟩ := h
    refine AbsInv.integral_eq_zero_of_translate μ _ m0 (χ m0) h1 fun m => ?_
    by_cases hm : m ∈ M
    · rw [Set.indicator_of_mem (by exact M.add_mem hm hm0), Set.indicator_of_mem (by exact hm), hχ, mul_comm]
    · have h2 : m + m0 ∉ M := fun h' => hm (by simpa using M.sub_mem h' hm0)
      rw [Set.indicator_of_notMem (by exact h2), Set.indicator_of_notMem (by exact hm), mul_zero]

end GlobalTheory.JR.WeilQuad.GaussStable

open GlobalTheory.JR.WeilQuad.GaussStable in

theorem GlobalTheory.JR.WeilQuad.exists_stableGauss : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ u : A.Kˣ, ∃ G, IsStableGauss A ψ x μ u G := by
  intro F E _ _ _ _ hU A ψ x μ ω h u
  classical
  obtain ⟨-, -, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  set β := EtMeas.formL A ((u * x : A.Kˣ) : A.K) with hβ
  set f : A.L → ℂ := fun y => A.psiK ψ ((u : A.K) * x * A.NL y) with hf
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hin : Continuous fun y : A.L => Algebra.trace F A.K ((u : A.K) * x * A.NL y) :=
    htr.comp (continuous_const.mul (GlobalTheory.JR.EtMeas.continuous_NL A))
  have hflc : IsLocallyConstant f := (isLocallyConstant_of_stdChar hψ).comp_continuous hin
  have hfc : Continuous f := hflc.continuous
  have hkey : ∀ y m, f (y + m) = f y * ψ (β m y) * f m := by
    intro y m
    simp only [hf, hβ, EtMeas.formL_apply, Units.val_mul, NL_add A, Et.psiK, mul_add, map_add,
      AddChar.map_add_eq_mul]
  have hf0 : f 0 = 1 := by simp [hf, NL_zero A, Et.psiK]
  obtain ⟨-, hsmall⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ A.L β
    (formL_symm_nondeg A (u * x)).1 (formL_symm_nondeg A (u * x)).2
  obtain ⟨M, N, hMU, hMo, hMc, hNo, hNc, hN, -⟩ :=
    hsmall {y | f y = 1} ((hflc.isOpen_fiber 1).mem_nhds hf0)
  have hfM : ∀ m ∈ M, f m = 1 := fun m hm => hMU hm
  have hMpos : μ.real (M : Set A.L) ≠ 0 :=
    (ENNReal.toReal_pos (hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne' hMc.measure_lt_top.ne).ne'
  refine ⟨∫ y in (N : Set A.L), f y ∂μ, M ⊔ N, AddSubgroup.isOpen_mono le_sup_left hMo, ?_, ?_⟩
  · refine (hMc.add hNc).of_isClosed_subset
      (AddSubgroup.isClosed_of_isOpen _ (AddSubgroup.isOpen_mono le_sup_left hMo)) ?_
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hz
    exact Set.add_mem_add ha hb
  intro Λ hΛo hΛc hle
  have hMΛ : M ≤ Λ := le_sup_left.trans hle
  have hNΛ : N ≤ Λ := le_sup_right.trans hle
  set iM : A.L → ℂ := (M : Set A.L).indicator (fun _ => 1) with hiM
  set iΛ : A.L → ℂ := (Λ : Set A.L).indicator (fun _ => 1) with hiΛ
  have hiMc : Continuous iM :=
    IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hMo, hMo⟩ continuous_const
  have hiΛc : Continuous iΛ :=
    IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hΛo, hΛo⟩ continuous_const
  let g : A.L → A.L → ℂ := fun m y => iM m * (iΛ y * f (y + m))
  have hgc : Continuous (Function.uncurry g) :=
    (hiMc.comp continuous_fst).mul ((hiΛc.comp continuous_snd).mul (hfc.comp (continuous_snd.add continuous_fst)))
  have hgs : HasCompactSupport (Function.uncurry g) := by
    refine HasCompactSupport.intro (hMc.prod hΛc) ?_
    rintro ⟨m, y⟩ hp
    simp only [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · have : iM m = 0 := by rw [hiM, Set.indicator_of_notMem hp]
      simp [Function.uncurry, g, this]
    · have : iΛ y = 0 := by rw [hiΛ, Set.indicator_of_notMem hp]
      simp [Function.uncurry, g, this]
  have hswap := integral_integral_swap_of_hasCompactSupport hgc hgs (μ := μ) (ν := μ)
  have hA : ∀ m, ∫ y, g m y ∂μ = iM m * ∫ y in (Λ : Set A.L), f y ∂μ := by
    intro m
    by_cases hm : m ∈ M
    · have e : ∀ y, iΛ y * f (y + m) = (Λ : Set A.L).indicator f (y + m) := by
        intro y
        by_cases hy : y ∈ Λ
        · rw [hiΛ, Set.indicator_of_mem (by exact hy), Set.indicator_of_mem (by exact Λ.add_mem hy (hMΛ hm)), one_mul]
        · have h2 : y + m ∉ Λ := fun h' => hy (by simpa using Λ.sub_mem h' (hMΛ hm))
          rw [hiΛ, Set.indicator_of_notMem (by exact hy), Set.indicator_of_notMem (by exact h2), zero_mul]
      simp only [g]
      rw [integral_const_mul]
      congr 1
      simp_rw [e]
      rw [integral_add_right_eq_self (μ := μ) ((Λ : Set A.L).indicator f) m,
        integral_indicator hΛo.measurableSet]
    · have h1 : iM m = 0 := by rw [hiM, Set.indicator_of_notMem (by exact hm)]
      simp [g, h1]
  have hB : ∀ y, ∫ m, g m y ∂μ = (N : Set A.L).indicator (fun y => (μ.real (M : Set A.L) : ℂ) * f y) y := by
    intro y
    have e : ∀ m, g m y = iΛ y * f y * (M : Set A.L).indicator (fun m => ψ (β m y)) m := by
      intro m
      by_cases hm : m ∈ M
      · have h1 : iM m = 1 := by rw [hiM, Set.indicator_of_mem (by exact hm)]
        have h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = ψ (β m y) :=
          Set.indicator_of_mem (by exact hm) _
        simp only [g]
        rw [h1, h2, hkey, hfM m hm]; ring
      · have h1 : iM m = 0 := by rw [hiM, Set.indicator_of_notMem (by exact hm)]
        have h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = 0 :=
          Set.indicator_of_notMem (by exact hm) _
        simp only [g]
        rw [h1, h2]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_indicator_char μ M hMo (fun m => ψ (β m y))
      (fun a b => by simp [map_add, AddChar.map_add_eq_mul])]
    by_cases hy : y ∈ N
    · rw [if_pos ((hN y).1 hy), Set.indicator_of_mem (by exact hy), hiΛ, Set.indicator_of_mem (by exact hNΛ hy)]
      ring
    · rw [if_neg (fun h' => hy ((hN y).2 h')), Set.indicator_of_notMem (by exact hy), mul_zero]
  have h1 : ∫ m, ∫ y, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (Λ : Set A.L), f y ∂μ := by
    simp_rw [hA]
    rw [integral_mul_const, hiM, integral_indicator_const _ hMo.measurableSet]
    simp
  have h2 : ∫ y, ∫ m, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (N : Set A.L), f y ∂μ := by
    simp_rw [hB]
    rw [integral_indicator hNo.measurableSet, integral_const_mul]
  have hmain := h1.symm.trans (hswap.trans h2)
  unfold gaussInt
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hMpos) hmain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIntegralClosureOfSeparableInvolutionAlgebr
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.IntegralFinite

open Matrix

theorem isIntegral_matrix_trace {R F : Type} [CommRing R] [Field F] [Algebra R F] {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n F) (hM : IsIntegral R M) : IsIntegral R M.trace := by
  first
  | exact @_root_.GlobalTheory.TargetStatementAlt.target
  | exact _root_.GlobalTheory.TargetStatementAlt.target
  | (apply _root_.GlobalTheory.TargetStatementAlt.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementAlt.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementAlt.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementAlt.target ..)

variable {K : UQ} (B : InvAlg K)

theorem isIntegral_trace {x : B.A} (hx : IsIntegral K.O x) :
    IsIntegral K.O (Algebra.trace K.E B.A x) := by
  let bs := Module.finBasis K.E B.A
  rw [Algebra.trace_eq_matrix_trace bs]
  exact isIntegral_matrix_trace _ (hx.map ((Algebra.leftMulMatrix bs).restrictScalars K.O))

theorem trace_mem_range {x : B.A} (hx : IsIntegral K.O x) :
    ∃ c : K.O, algebraMap K.O K.E c = Algebra.trace K.E B.A x :=
  IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_trace B hx)

theorem finite_integralClosure :
    ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Module.Finite K.O (integralClosure K.O B.A) := by
  intro K B hsep
  classical
  let bs := Module.finBasis K.E B.A
  haveI : Algebra.IsAlgebraic K.O K.E := IsLocalization.isAlgebraic K.E (nonZeroDivisors K.O)
  haveI : Algebra.IsAlgebraic K.O B.A := Algebra.IsAlgebraic.trans K.O K.E B.A
  obtain ⟨y, hy, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples K.O (Finset.univ.image bs)
  have hy' : algebraMap K.O K.E y ≠ 0 := by
    intro h
    exact hy (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))
  let b := bs.isUnitSMul (w := fun _ => algebraMap K.O K.E y) (fun _ => (Ne.isUnit hy'))
  have hbint : ∀ i, IsIntegral K.O (b i) := by
    intro i
    have h := hint (bs i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    simpa [b, Module.Basis.isUnitSMul_apply, algebraMap_smul] using h
  have hnd : (Algebra.traceForm K.E B.A).Nondegenerate := by
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · exact Centraliser.eq_zero_of_trace_mul B hsep a (fun z => by simpa [Algebra.traceForm_apply] using ha z)
    · exact Centraliser.eq_zero_of_trace_mul B hsep a
        (fun z => by simpa [Algebra.traceForm_apply, mul_comm] using ha z)
  let d := (Algebra.traceForm K.E B.A).dualBasis hnd b
  have hle : Subalgebra.toSubmodule (integralClosure K.O B.A) ≤ Submodule.span K.O (Set.range d) := by
    intro x hx
    have hx' : IsIntegral K.O x := hx
    rw [← d.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := trace_mem_range B (hx'.mul (hbint i))
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, ← hc, algebraMap_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)
  haveI : IsNoetherian K.O (Submodule.span K.O (Set.range d)) :=
    isNoetherian_span_of_finite K.O (Set.finite_range d)
  haveI : IsNoetherian K.O (Subalgebra.toSubmodule (integralClosure K.O B.A)) := isNoetherian_of_le hle
  exact Module.IsNoetherian.finite K.O (Subalgebra.toSubmodule (integralClosure K.O B.A))

end GlobalTheory.UnitLemma.IntegralFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityLaurentShiftEqSumSenStatement
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genEigenMultiplicity_laurentShift_eq_sum_sen : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (m : ℕ) (x : k), qmult g (sh a N) (sh (a + m) N) x = ∑ j ∈ Finset.range m, sen g N (x + (a + j : ℤ)) := by
  first | exact @GlobalTheory.PhiGam.Range.qmult_sh_range | exact GlobalTheory.PhiGam.Range.qmult_sh_range | (intros; apply GlobalTheory.PhiGam.Range.qmult_sh_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantImageOpenClosedLocalSectionsStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_image_openClosed_local_sections : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (a₀ : Inv r F), Delta a₀ ≠ 0 → ((¬ ∃ X : Hn r F E, HasInv X a₀) → ∀ᶠ a in 𝓝 a₀, ¬ ∃ X : Hn r F E, HasInv X a) ∧ ((∃ X : Hn r F E, HasInv X a₀) → ∃ (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ ContinuousOn s Ω ∧ (∀ a ∈ Ω, Delta a ≠ 0 ∧ HasInv (s a) a) ∧ ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C}) := by
  first | exact @GlobalTheory.JR.image_openClosed_section | exact GlobalTheory.JR.image_openClosed_section | (intros; apply GlobalTheory.JR.image_openClosed_section <;> assumption)
end

