import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0002

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfHOmega
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable {W : LocWach PD LL O v n}

theorem Pf_HOmega_pow_card (δ : W.Gam) (hδ : δ ∈ W.DelF) : δ ^ W.DelF.card = 1 := by
  have hH : ∀ g : W.Gam, g ∈ CommGroup.torsion W.Gam ↔ g ∈ W.DelF := by
    intro g
    rw [W.DelF_def, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  have hset : ((CommGroup.torsion W.Gam : Subgroup W.Gam) : Set W.Gam) = (W.DelF : Set W.Gam) := by
    ext g
    simp only [SetLike.mem_coe]
    exact hH g
  have hcardH : Nat.card (CommGroup.torsion W.Gam) = W.DelF.card := by
    rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hd := orderOf_dvd_natCard (⟨δ, (hH δ).2 hδ⟩ : CommGroup.torsion W.Gam)
  rw [Subgroup.orderOf_mk, hcardH] at hd
  exact orderOf_dvd_iff_pow_eq_one.1 hd

theorem hω_holds (hcard : W.DelF.card = PD.p - 1) (hinj : Function.Injective (algebraMap O LL))
    (ιZ : ℤ_[PD.p] →+* O) :
    ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF, algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ω.1) := by
  classical
  intro ω
  have hpos : 0 < PD.p - 1 := by have := PD.hp.two_le; omega
  set f : W.Gam → LL := fun g => algebraMap O LL (W.χΓ g : O) with hf
  have hAcard : (W.DelF.image f).card = PD.p - 1 := by
    rw [Finset.card_image_of_injOn, hcard]
    intro x _ y _ hxy
    apply W.χΓ_inj
    apply Units.ext
    exact hinj hxy
  have hARt : W.DelF.image f ⊆ Polynomial.nthRootsFinset (PD.p - 1) (1 : LL) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    rw [Polynomial.mem_nthRootsFinset hpos]
    have h1 : g ^ (PD.p - 1) = 1 := hcard ▸ Pf_HOmega_pow_card g hg
    simp only [hf]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h1, map_one, Units.val_one, map_one]
  have hRt : (Polynomial.nthRootsFinset (PD.p - 1) (1 : LL)).card ≤ PD.p - 1 := by
    unfold Polynomial.nthRootsFinset
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  have hEq : W.DelF.image f = Polynomial.nthRootsFinset (PD.p - 1) (1 : LL) :=
    Finset.eq_of_subset_of_card_le hARt (by omega)
  have hωR : algebraMap O LL (ιZ ω.1) ∈ Polynomial.nthRootsFinset (PD.p - 1) (1 : LL) := by
    rw [Polynomial.mem_nthRootsFinset hpos, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ω.2,
      Units.val_one, map_one, map_one]
  rw [← hEq] at hωR
  obtain ⟨g, hg, hgω⟩ := Finset.mem_image.1 hωR
  exact ⟨g, hg, hgω⟩

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvBasisCmp
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {T : LocLat G Qp LL O}

theorem lvBasis_cmp_congr {a b : W.DD T} (ha : a ∈ W.N T) (hb : b ∈ W.N T) (h : a = b) :
    W.cmp T ⟨a, ha⟩ = W.cmp T ⟨b, hb⟩ := by
  subst h
  rfl

theorem lvBasis_cmp_add {a b : W.DD T} (ha : a ∈ W.N T) (hb : b ∈ W.N T) (hab : a + b ∈ W.N T) :
    W.cmp T ⟨a + b, hab⟩ = W.cmp T ⟨a, ha⟩ + W.cmp T ⟨b, hb⟩ := by
  rw [← map_add]
  rfl

theorem lvBasis_letE_idem (i : ZMod n) (x : W.DD T) :
    (letE i : LetA O n) • (letE i : LetA O n) • x = (letE i : LetA O n) • x := by
  rw [smul_smul, letE_mul_self]

theorem lvBasis_sum_letE : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem lvBasis_cmp_of_eq {w z y : W.DD T} (hw : w ∈ W.N T) (hz : z ∈ W.N T) (hy : y ∈ W.N T)
    (o : O) (h : y = o • w + (letπ : LetA O n) • z) :
    W.cmp T ⟨y, hy⟩ = algebraMap O LL o • W.cmp T ⟨w, hw⟩ := by
  have e : (⟨y, hy⟩ : ↥(W.N T)) = o • ⟨w, hw⟩ + (letπ : LetA O n) • ⟨z, hz⟩ := Subtype.ext h
  rw [e, map_add, W.cmp_smul, W.cmp_π, add_zero]

theorem lvBasis_cmp_smul_const {w : W.DD T} (hw : w ∈ W.N T) (a : LetA O n) (o : O)
    (ha : ∀ j, PowerSeries.constantCoeff (a j) = o) (h : a • w ∈ W.N T) :
    W.cmp T ⟨a • w, h⟩ = algebraMap O LL o • W.cmp T ⟨w, hw⟩ := by
  have hd : ∀ j, (PowerSeries.X : PowerSeries O) ∣ a j - PowerSeries.C o := fun j =>
    PowerSeries.X_dvd_iff.2 (by rw [map_sub, ha j, PowerSeries.constantCoeff_C, sub_self])
  choose b hb using hd
  have ea : a = o • (1 : LetA O n) + (letπ : LetA O n) * b := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, Pi.mul_apply, letπ]
    rw [PowerSeries.smul_eq_C_mul, mul_one, ← hb j]
    ring
  refine lvBasis_cmp_of_eq hw ((W.N T).smul_mem b hw) h o ?_
  rw [ea, add_smul, mul_smul, smul_assoc, one_smul]

theorem lvBasis_cmp_smul_letter {w : W.DD T} (hw : w ∈ W.N T) (i : ZMod n)
    (hwi : (letE i : LetA O n) • w = w) (a : LetA O n) (h : a • w ∈ W.N T) :
    W.cmp T ⟨a • w, h⟩ = algebraMap O LL (PowerSeries.constantCoeff (a i)) • W.cmp T ⟨w, hw⟩ := by
  obtain ⟨b, hb⟩ := PowerSeries.X_dvd_iff.2
    (by rw [map_sub, PowerSeries.constantCoeff_C, sub_self] :
      PowerSeries.constantCoeff (a i - PowerSeries.C (PowerSeries.constantCoeff (a i))) = 0)
  refine lvBasis_cmp_of_eq hw ((W.N T).smul_mem (Pi.single i b) hw) h _ ?_
  have ea : a * letE i = PowerSeries.constantCoeff (a i) • (letE i : LetA O n) + letπ * Pi.single i b := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, letE, letπ, Pi.single_eq_same,
        PowerSeries.smul_eq_C_mul, mul_one]
      rw [← hb]
      ring
    · simp [letE, letπ, hj]
  calc a • w = a • ((letE i : LetA O n) • w) := by rw [hwi]
    _ = (a * letE i) • w := by rw [mul_smul]
    _ = _ := by rw [ea, add_smul, smul_assoc, hwi, mul_smul]

theorem lvBasis_q₀_const : PowerSeries.constantCoeff W.q₀ = (PD.p : O) := by
  have h1 : PowerSeries.coeff 1 (PowerSeries.X * W.q₀) = PowerSeries.constantCoeff W.q₀ := by
    simp
  rw [← h1, W.q₀_def]
  have e : (1 + PowerSeries.X : PowerSeries O) ^ PD.p - 1 =
      (((1 + Polynomial.X) ^ PD.p - 1 : Polynomial O) : PowerSeries O) := by
    simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one,
      Polynomial.coe_X]
  rw [e, Polynomial.coeff_coe, Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow,
    Polynomial.coeff_one]
  simp

theorem lvBasis_Q_const (j : ZMod n) : PowerSeries.constantCoeff (W.Q j) = (PD.p : O) := by
  have hφ : ∀ (a : LetA O n) (j : ZMod n),
      PowerSeries.constantCoeff (W.φA a j) = PowerSeries.constantCoeff (a (j - 1)) := by
    intro a j
    have e : W.φA a j = W.φ₀ (a (j - 1)) := rfl
    rw [e, constCoeff_algHom W.φ₀ (by rw [W.φ₀_X, map_mul, PowerSeries.constantCoeff_X, zero_mul])]
  have key : ∀ (k : ℕ) (j : ZMod n), PowerSeries.constantCoeff (((W.φA ^ k) W.q) j) = (PD.p : O) := by
    intro k
    induction k with
    | zero => intro j; exact lvBasis_q₀_const
    | succ k ih => intro j; rw [pow_succ', AlgHom.mul_apply, hφ, ih]
  exact key _ j

theorem lvBasis_cmp_Qpow {w : W.DD T} (hw : w ∈ W.N T) (k : ℕ) (h : W.Q ^ k • w ∈ W.N T) :
    W.cmp T ⟨W.Q ^ k • w, h⟩ = ((PD.p : ℕ) : LL) ^ k • W.cmp T ⟨w, hw⟩ := by
  rw [lvBasis_cmp_smul_const hw _ (((PD.p : ℕ) : O) ^ k)
    (fun j => by rw [Pi.pow_apply, map_pow, lvBasis_Q_const]) h, map_pow, map_natCast]

theorem lvBasis_p_ne_zero (W : LocWach PD LL O v n) : ((PD.p : ℕ) : LL) ≠ 0 := by
  intro h0
  have hv := W.v_l
  rw [h0, AddValuation.map_zero] at hv
  exact WithTop.top_ne_one hv

theorem lvBasis_letter_span (hspan : Submodule.span LL (Set.range (W.cmp T)) = Dcris PD T.ρ)
    (j : ZMod n) {d : T.V ⊗[Qp] B} (hd : d ∈ DcrisL PD T.ρ (W.emb j)) :
    d ∈ Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T ((letE j : LetA O n) • x)) := by
  classical
  have hd' : d ∈ Submodule.span LL (Set.range (W.cmp T)) := by
    rw [hspan]
    exact ((lvBasis_mem_DcrisL PD T.ρ _ d).1 hd).1
  obtain ⟨f, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hd'
  let z : ZMod n → T.V ⊗[Qp] B := fun i => f.sum fun x a => a • W.cmp T ((letE i : LetA O n) • x)
  have hzi : ∀ i, z i ∈ DcrisL PD T.ρ (W.emb i) := fun i =>
    Submodule.finsuppSum_mem _ _ _ _ fun x _ => Submodule.smul_mem _ _ (W.cmp_letter T i x)
  have hzj : z j ∈ Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T ((letE j : LetA O n) • x)) :=
    Submodule.finsuppSum_mem _ _ _ _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hzs : ∑ i, z i = f.sum fun x a => a • W.cmp T x := by
    simp only [z, Finsupp.sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.smul_sum, ← map_sum, ← Finset.sum_smul, lvBasis_sum_letE, one_smul]
  have key := lvBasis_indep W.emb W.emb_bij.1
    (fun i => z i - if i = j then (f.sum fun x a => a • W.cmp T x) else 0) (fun i c => by
      have h1 := ((lvBasis_mem_DcrisL PD T.ρ _ _).1 (hzi i)).2 c
      split_ifs with hij
      · subst hij
        rw [map_sub, smul_sub, h1, ((lvBasis_mem_DcrisL PD T.ρ _ _).1 hd).2 c]
      · rw [sub_zero, h1]) (by simp [Finset.sum_sub_distrib, hzs]) j
  rw [if_pos rfl, sub_eq_zero] at key
  rw [← key]
  exact hzj

theorem lvBasis_cmp_mem_φ (h3 : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T),
      W.cmp T ⟨_, hk⟩ = ((PD.p : LL) ^ k) • φVB PD (LL := LL) (V := T.V) (W.cmp T x))
    (j : ZMod n) {y : W.DD T} (hy : y ∈ W.N T) (hyj : (letE j : LetA O n) • y = y) :
    W.cmp T ⟨y, hy⟩ ∈ (Dcris PD T.ρ).map (φVB PD (LL := LL) (V := T.V)) := by
  set U := (Dcris PD T.ρ).map (φVB PD (LL := LL) (V := T.V)) with hU
  have key : ∀ z ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))),
      ∃ m : ℕ, ∀ i, ∃ h : (letE i : LetA O n) • W.Q ^ m • z ∈ W.N T, W.cmp T ⟨_, h⟩ ∈ U := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨k, hk⟩ := W.N_φ T x hx
      have hk2 : W.Q ^ k • W.φD T x ∈ W.N T := hk
      refine ⟨k, fun i => ⟨(W.N T).smul_mem _ hk2, ?_⟩⟩
      have hx' : (letE (i - 1) : LetA O n) • x ∈ W.N T := (W.N T).smul_mem _ hx
      have he : (letE i : LetA O n) • W.Q ^ k • W.φD T x =
          W.Q ^ k • W.φD T ((letE (i - 1) : LetA O n) • x) := by
        rw [φD_smulA W, φA_letE W, smul_comm]
      have hk' : W.Q ^ k • W.φD T ((letE (i - 1) : LetA O n) • x) ∈ W.N T := he ▸ (W.N T).smul_mem _ hk2
      rw [lvBasis_cmp_congr _ hk' he]
      rw [h3 ⟨_, hx'⟩ k hk']
      exact U.smul_mem _ (Submodule.mem_map_of_mem (W.cmp_mem T _))
    | zero =>
      refine ⟨0, fun i => ⟨by simp, ?_⟩⟩
      rw [lvBasis_cmp_congr _ (W.N T).zero_mem (by simp)]
      have h0 : W.cmp T ⟨0, (W.N T).zero_mem⟩ = 0 := map_zero (W.cmp T)
      rw [h0]
      exact U.zero_mem
    | add z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨m₁, hm₁⟩ := h₁
      obtain ⟨m₂, hm₂⟩ := h₂
      refine ⟨m₁ + m₂, fun i => ?_⟩
      obtain ⟨ha, hca⟩ := hm₁ i
      obtain ⟨hb, hcb⟩ := hm₂ i
      have ha' := (W.N T).smul_mem (W.Q ^ m₂) ha
      have hb' := (W.N T).smul_mem (W.Q ^ m₁) hb
      have he : (letE i : LetA O n) • W.Q ^ (m₁ + m₂) • (z₁ + z₂) =
          W.Q ^ m₂ • (letE i : LetA O n) • W.Q ^ m₁ • z₁ +
            W.Q ^ m₁ • (letE i : LetA O n) • W.Q ^ m₂ • z₂ := by
        simp only [smul_add, smul_smul]
        congr 1 <;> congr 1 <;> ring
      refine ⟨he ▸ (W.N T).add_mem ha' hb', ?_⟩
      rw [lvBasis_cmp_congr _ ((W.N T).add_mem ha' hb') he, lvBasis_cmp_add ha' hb',
        lvBasis_cmp_Qpow ha, lvBasis_cmp_Qpow hb]
      exact U.add_mem (U.smul_mem _ hca) (U.smul_mem _ hcb)
    | smul a z _ hz =>
      obtain ⟨m, hm⟩ := hz
      refine ⟨m, fun i => ?_⟩
      obtain ⟨h, hc⟩ := hm i
      have he : (letE i : LetA O n) • W.Q ^ m • (a • z) = a • (letE i : LetA O n) • W.Q ^ m • z := by
        rw [smul_comm (W.Q ^ m) a z, smul_comm (letE i : LetA O n) a]
      refine ⟨he ▸ (W.N T).smul_mem a h, ?_⟩
      rw [lvBasis_cmp_congr _ ((W.N T).smul_mem a h) he,
        lvBasis_cmp_smul_letter h i (lvBasis_letE_idem i _)]
      exact U.smul_mem _ hc
  obtain ⟨k, hk⟩ := W.N_φinv T y hy
  have hk2 : W.Q ^ k • y ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) := hk
  obtain ⟨m, hm⟩ := key _ hk2
  obtain ⟨h, hc⟩ := hm j
  have he : (letE j : LetA O n) • W.Q ^ m • W.Q ^ k • y = W.Q ^ (m + k) • y := by
    rw [smul_comm (letE j : LetA O n), smul_comm (letE j : LetA O n), hyj, pow_add, mul_smul]
  rw [lvBasis_cmp_congr _ ((W.N T).smul_mem _ hy) he, lvBasis_cmp_Qpow hy] at hc
  have hc2 := U.smul_mem (((PD.p : ℕ) : LL) ^ (m + k))⁻¹ hc
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (lvBasis_p_ne_zero W)), one_smul] at hc2

theorem lvBasis_letter_pre (hspan : Submodule.span LL (Set.range (W.cmp T)) = Dcris PD T.ρ)
    (h3 : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T),
      W.cmp T ⟨_, hk⟩ = ((PD.p : LL) ^ k) • φVB PD (LL := LL) (V := T.V) (W.cmp T x))
    (j : ZMod n) {d : T.V ⊗[Qp] B} (hd : d ∈ DcrisL PD T.ρ (W.emb j)) :
    ∃ d' ∈ DcrisL PD T.ρ (W.emb (j - 1)), φVB PD (LL := LL) (V := T.V) d' = d := by
  have hdU : d ∈ (Dcris PD T.ρ).map (φVB PD (LL := LL) (V := T.V)) := by
    refine Submodule.span_le.2 ?_ (lvBasis_letter_span hspan j hd)
    rintro _ ⟨x, rfl⟩
    exact lvBasis_cmp_mem_φ h3 j ((W.N T).smul_mem _ x.2) (lvBasis_letE_idem j _)
  obtain ⟨d', hd'D, rfl⟩ := hdU
  refine ⟨d', (lvBasis_mem_DcrisL PD T.ρ _ d').2 ⟨hd'D, fun c => ?_⟩, rfl⟩
  apply lvBasis_φ_inj PD (LL := LL) (V := T.V)
  rw [← lvBasis_φ_mul, ((lvBasis_mem_DcrisL PD T.ρ _ _).1 hd).2, map_smul]
  congr 1
  rw [← W.emb_σ (j - 1), AlgHom.comp_apply, sub_add_cancel]

theorem lvBasis_φpow_letter (i : ZMod n) (k : ℕ) {x : T.V ⊗[Qp] B} (hx : x ∈ DcrisL PD T.ρ (W.emb i)) :
    ((φVB PD (LL := LL) (V := T.V)) ^ k) x ∈ DcrisL PD T.ρ (W.emb (i + k)) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, Nat.cast_succ, ← add_assoc]
    exact lvBasis_φ_letter PD T.ρ (W.emb_σ (i + k)) ih

theorem lvBasis_φpow_pre (hspan : Submodule.span LL (Set.range (W.cmp T)) = Dcris PD T.ρ)
    (h3 : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T),
      W.cmp T ⟨_, hk⟩ = ((PD.p : LL) ^ k) • φVB PD (LL := LL) (V := T.V) (W.cmp T x))
    (c : ZMod n) (k : ℕ) {d : T.V ⊗[Qp] B} (hd : d ∈ DcrisL PD T.ρ (W.emb c)) :
    ∃ d' ∈ DcrisL PD T.ρ (W.emb (c - k)), ((φVB PD (LL := LL) (V := T.V)) ^ k) d' = d := by
  induction k with
  | zero => exact ⟨d, by simpa using hd, by simp⟩
  | succ k ih =>
    obtain ⟨d₁, hd₁, rfl⟩ := ih
    obtain ⟨d', hd', rfl⟩ := lvBasis_letter_pre hspan h3 _ hd₁
    refine ⟨d', ?_, ?_⟩
    · rw [Nat.cast_succ, ← sub_sub]
      exact hd'
    · rw [pow_succ, Module.End.mul_apply]

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvDelta
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

section Graded

variable {LL Ks : Type} [Field LL] [CommRing Ks] [Algebra LL Ks]

theorem grdB_zero' (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) : grdB τ a 0 = 0 := by
  ext n
  show algebraMap LL Ks ((a ^ n : LLˣ) : LL) * τ ((0 : HahnSeries ℤ Ks).coeff n) = (0 : HahnSeries ℤ Ks).coeff n
  simp

theorem grdB_one' (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) : grdB τ a 1 = 1 := by
  ext n
  show algebraMap LL Ks ((a ^ n : LLˣ) : LL) * τ ((1 : HahnSeries ℤ Ks).coeff n) = (1 : HahnSeries ℤ Ks).coeff n
  by_cases h : n = 0
  · subst h
    simp
  · simp [HahnSeries.coeff_one, h]

theorem grdB_mul' (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) (x y : HahnSeries ℤ Ks) :
    grdB τ a (x * y) = grdB τ a x * grdB τ a y := by
  ext n
  show algebraMap LL Ks ((a ^ n : LLˣ) : LL) * τ ((x * y).coeff n) = (grdB τ a x * grdB τ a y).coeff n
  rw [HahnSeries.coeff_mul, HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
  symm
  have hsub : ∀ ij : ℤ × ℤ, ij ∈ Finset.antidiagonal (grdB τ a x).isPWO_support
      (grdB τ a y).isPWO_support n → ij ∈ Finset.antidiagonal x.isPWO_support y.isPWO_support n := by
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij ⊢
    refine ⟨fun h0 => hij.1 ?_, fun h0 => hij.2.1 ?_, hij.2.2⟩
    · change algebraMap LL Ks ((a ^ ij.1 : LLˣ) : LL) * τ (x.coeff ij.1) = 0
      rw [h0, map_zero, mul_zero]
    · change algebraMap LL Ks ((a ^ ij.2 : LLˣ) : LL) * τ (y.coeff ij.2) = 0
      rw [h0, map_zero, mul_zero]
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.mem_antidiagonal] at hij
    have hn : ij.1 + ij.2 = n := hij.2.2
    change (algebraMap LL Ks ((a ^ ij.1 : LLˣ) : LL) * τ (x.coeff ij.1)) *
      (algebraMap LL Ks ((a ^ ij.2 : LLˣ) : LL) * τ (y.coeff ij.2)) = _
    rw [← hn, zpow_add, Units.val_mul, map_mul, map_mul]
    ring
  · intro ij hmem hnot
    rw [Finset.mem_antidiagonal] at hmem hnot
    by_cases h1 : (grdB τ a x).coeff ij.1 = 0
    · rw [h1, zero_mul]
    · by_cases h2 : (grdB τ a y).coeff ij.2 = 0
      · rw [h2, mul_zero]
      · exact absurd ⟨h1, h2, hmem.2.2⟩ hnot

theorem grdB_ringInverse (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) {X : HahnSeries ℤ Ks} (hX : grdB τ a X = X) :
    grdB τ a (Ring.inverse X) = Ring.inverse X := by
  by_cases hu : IsUnit X
  · obtain ⟨u, rfl⟩ := hu
    rw [Ring.inverse_unit]
    have h1 : grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks) * ↑u = 1 := by
      conv_lhs => rw [← hX]
      rw [← grdB_mul', Units.inv_mul, grdB_one']
    calc grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks)
        = grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks) * (↑u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
      _ = (grdB τ a (↑u⁻¹ : HahnSeries ℤ Ks) * ↑u) * ↑u⁻¹ := by ring
      _ = ↑u⁻¹ := by rw [h1, one_mul]
  · rw [Ring.inverse_non_unit _ hu, grdB_zero']

theorem ofPS_coeff_neg {R : Type} [CommRing R] (x : PowerSeries R) {i : ℤ} (hi : i < 0) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff i = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_of_notMem_range (by
    rintro ⟨m, hm⟩
    simp at hm
    omega)

end Graded

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

theorem val_sub_toZModPow (W : LocWach PD LL O v n) (valRing : ValRing O v) (ιZ : ℤ_[PD.p] →+* O)
    (ω : ℤ_[PD.p]) (N : ℕ) :
    ((N : ℕ) : WithTop ℚ) ≤
      v (algebraMap O LL (ιZ ω) - (((PadicInt.toZModPow N ω : ZMod (PD.p ^ N)).val : ℕ) : LL)) := by
  have : NeZero (PD.p ^ N) := ⟨pow_ne_zero _ PD.hp.ne_zero⟩
  have hk : ω - (((PadicInt.toZModPow N ω : ZMod (PD.p ^ N)).val : ℕ) : ℤ_[PD.p]) ∈
      RingHom.ker (PadicInt.toZModPow (p := PD.p) N) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
  obtain ⟨y, hy⟩ := hk
  have e : algebraMap O LL (ιZ ω) - (((PadicInt.toZModPow N ω : ZMod (PD.p ^ N)).val : ℕ) : LL) =
      ((PD.p : ℕ) : LL) ^ N * algebraMap O LL (ιZ y) := by
    rw [← map_natCast (algebraMap O LL), ← map_natCast ιZ, ← map_sub, ← map_sub, hy, map_mul, map_mul,
      map_pow, map_pow, map_natCast, map_natCast]
  rw [e, AddValuation.map_mul, AddValuation.map_pow, W.v_l, nsmul_one]
  exact le_add_of_nonneg_right (valRing.2.2 _)

variable {W : LocWach PD LL O v n}

theorem delta_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (c : ZMod n)
    (lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ f : LetA O n,
      W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (hω : ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF, algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ω.1))
    (valRing : ValRing O v) :
    DeltaRho hR uZ ιZ c := by
  intro s j a
  obtain ⟨g, hg, hχ⟩ := hω j
  apply HahnSeries.ext
  funext i
  by_cases hi : i < 0
  · show algebraMap LL (KsW W s) ((((levW W uZ ιZ s).a j) ^ i : LLˣ) : LL) *
        ((levW W uZ ιZ s).τ j) ((HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff i) =
      (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff i
    rw [ofPS_coeff_neg _ hi, map_zero, mul_zero]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hi)
    show algebraMap LL (KsW W s) ((((levW W uZ ιZ s).a j) ^ (k : ℤ) : LLˣ) : LL) *
        ((levW W uZ ιZ s).τ j) ((HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff (k : ℤ)) =
      (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff (k : ℤ)
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    have hc : ∀ ζ' : Rs LL PD.p s, (PowerSeries.coeff k (rhoL hR c s a)) ζ' =
        PowerSeries.coeff k (W.lev c (ζ' : LL) ((baseIdOf hR).d a)) := fun ζ' => by
      show Pi.evalRingHom (fun _ => LL) ζ' (PowerSeries.coeff k (rhoL hR c s a)) = _
      rw [← PowerSeries.coeff_map, map_eval_rhoL]
      rfl
    funext ζ
    change ((((levW W uZ ιZ s).a j) ^ (k : ℤ) : LLˣ) : LL) *
      (PowerSeries.coeff k (rhoL hR c s a)) (powR LL PD.p s (redU PD.p s j.1) ζ) =
      (PowerSeries.coeff k (rhoL hR c s a)) ζ
    rw [hc, hc]
    have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) := (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
    have hv := val_sub_toZModPow W valRing ιZ (j.1 : ℤ_[PD.p]) (s + 1)
    rw [← hχ] at hv
    have hL := lev_Γ g c ζ _ (s + 1) _ hprim hv rfl ((baseIdOf hR).d a)
    rw [BaseId.γA_Δ _ g hg] at hL
    rw [hL, PowerSeries.coeff_rescale, hχ]
    congr 1

theorem loclInv_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (T : LocLat G Qp LL O)
    (c : ZMod n) {r : ℕ} (Λ : PowerSeries O) (lam : Fin r → Dc W T c) (hΔ : DeltaRho hR uZ ιZ c) :
    LocLInv hR uZ ιZ T c Λ lam := by
  intro s y j
  rw [Level.δ]
  unfold locLF
  rw [graded_semilinear_holds, grdB_ringInverse _ _ (hΔ s j Λ), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [graded_semilinear_holds, hΔ s j (y k), SlopeTestRemainingChoices.grd_cst]

end Formalism.MainNotions.N.Ln03.Pf
end
end

