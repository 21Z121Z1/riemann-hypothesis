import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.InFPOfMul
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.FrobeniusPowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace Formalism.MainNotions.N.Ln17.PCutBoundRep

variable (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem γ_smul (a : LetA O n) (x : W.DD T) : W.γ T (a • x) = W.γA W.gam a • W.γ T x :=
  GS.γD_smulA W T W.gam a x

theorem γA_lA (k : ℕ) : W.γA W.gam (lA W ^ k) = lA W ^ k := by
  simp only [lA, map_pow, map_natCast]

theorem φD_smulA (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem φpow_smulA (e : ℕ) (a : LetA O n) (x : W.DD T) :
    ((W.φD T) ^ e) (a • x) = (W.φA ^ e) a • ((W.φD T) ^ e) x := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih, φD_smulA, Module.End.mul_apply]
      <;> rfl

theorem γ_φpow (e : ℕ) (x : W.DD T) : W.γ T (((W.φD T) ^ e) x) = ((W.φD T) ^ e) (W.γ T x) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    exact (W.φγ_comm T W.gam _).symm

theorem γ_Δ {x : W.DD T} (h : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    ∀ δ ∈ W.DelF, W.γD T δ (W.γ T x) = W.γ T x := by
  intro δ hδ
  show W.γD T δ (W.γD T W.gam x) = W.γD T W.gam x
  rw [← W.γD_mul, mul_comm, W.γD_mul, h δ hδ]

theorem γ_NΔ (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {x : W.DD T} (hx : x ∈ W.NΔ T) :
    W.γ T x ∈ W.NΔ T := by
  have hx' : x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := hx
  show W.γ T x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (W.γ T x) = W.γ T x
  exact ⟨(hP2 T hT).1 W.gam x hx'.1, γ_Δ W hx'.2⟩

theorem γ_NΔi (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {c : ZMod n} {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (W.γ T x) := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨γ_NΔ W hT hP2 h1, ?_⟩
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.1 h2
  refine Submodule.mem_map.2 ⟨W.γ T z, (hP2 T hT).1 W.gam z hz, ?_⟩
  rw [← hzx]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [γ_smul, GS.γA_letE]

theorem γ_Pp (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {c : ZMod n} {e : ℕ} {y : W.DD T}
    (hy : y ∈ Pp W T c e) : W.γ T y ∈ Pp W T c e := by
  have key : Pp W T c e ≤ (Pp W T c e).comap (W.γ T).toAddMonoidHom := by
    unfold Pp
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    refine AddSubgroup.mem_comap.2 ?_
    show W.γ T (a • ((W.φD T) ^ e) x) ∈ _
    rw [γ_smul, γ_φpow]
    exact AddSubgroup.subset_closure ⟨_, GS.γA_mem W W.gam ha, _, γ_NΔi W hT hP2 hx, rfl⟩
  exact key hy

theorem γ_InFP (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {c : ZMod n} {e : ℕ} {f : LetA O n}
    {x : W.DD T} (h : InFP W T c e f x) : InFP W T c e (W.γA W.gam f) (W.γ T x) := by
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨W.γ T y, γ_Pp W hT hP2 hy, γ_smul W f y⟩

theorem inMultiple_of_mul {c : ZMod n} {e : ℕ} {f g : LetA O n} (hg : g ∈ W.AΔ) {x : W.DD T}
    (h : InFP W T c e (f * g) x) : InFP W T c e f x := by
  obtain ⟨y, hy, rfl⟩ := h
  refine ⟨g • y, ?_, mul_smul f g y⟩
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x', hx', rfl⟩ := hz
    apply AddSubgroup.subset_closure
    exact ⟨g * a, mul_mem hg ha, x', hx', (mul_smul g a _).symm⟩
  | zero => rw [smul_zero]; exact (Pp W T c e).zero_mem
  | add u v _ _ hu hv => rw [smul_add]; exact (Pp W T c e).add_mem hu hv
  | neg u _ hu => rw [smul_neg]; exact (Pp W T c e).neg_mem hu

theorem inMultiple_zero {c : ZMod n} {e : ℕ} {f : LetA O n} : InFP W T c e f 0 :=
  ⟨0, (Pp W T c e).zero_mem, (smul_zero f).symm⟩

theorem inMultiple_sum {c : ZMod n} {e : ℕ} {f : LetA O n} {ι : Type} (s : Finset ι) (x : ι → W.DD T)
    (h : ∀ i ∈ s, InFP W T c e f (x i)) : InFP W T c e f (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact inMultiple_zero W
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨y, hy, hxy⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨y', hy', hxy'⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨y + y', (Pp W T c e).add_mem hy hy', by rw [hxy, hxy', smul_add]⟩

theorem InI_γ (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {w : W.DD T}
    (h : InI W T c w) : InI W T c (W.γ T w) := by
  obtain ⟨h1, h2, ⟨y, hy, hyc, hxy⟩⟩ := h
  have h1 : (letE (O := O) c : LetA O n) • w = w := h1
  have h2 : ∀ δ ∈ W.DelF, W.γD T δ w = w := h2
  obtain ⟨u, hu, hγπ⟩ := hpi0
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • W.γ T w = W.γ T w
    rw [← GS.γA_letE W W.gam c, ← γ_smul, h1]
  · exact γ_Δ W h2
  · refine ⟨u • W.γ T y, TypesA.NΔ_smul W hu (γ_NΔ W hT hP2 hy), ?_, ?_⟩
    · rw [smul_comm, ← GS.γA_letE W W.gam c, ← γ_smul, hyc]
    · have : W.γ T (W.γ T w) - W.γ T w = W.γ T (W.γ T w - w) := by rw [map_sub]
      rw [this, hxy, γ_smul, hγπ, mul_smul]

theorem InI_smulA {c : ZMod n} {a : LetA O n} (ha : a ∈ W.AΔ) (ha' : W.γA W.gam a = a) {w : W.DD T}
    (h : InI W T c w) : InI W T c (a • w) := by
  obtain ⟨h1, h2, h3⟩ := h
  have h1 : (letE (O := O) c : LetA O n) • w = w := h1
  have h2 : ∀ δ ∈ W.DelF, W.γD T δ w = w := h2
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • (a • w) = a • w
    rw [smul_comm, h1]
  · show ∀ δ ∈ W.DelF, W.γD T δ (a • w) = a • w
    intro δ hδ
    rw [GS.γD_smulA, ha δ hδ, h2 δ hδ]
  · have : W.γ T (a • w) - a • w = a • (W.γ T w - w) := by rw [γ_smul, ha', smul_sub]
    rw [this]
    exact TypesA.InFNc_smul W ha h3

theorem InI_smulO {c : ZMod n} (o : O) {w : W.DD T} (h : InI W T c w) : InI W T c (o • w) := by
  obtain ⟨h1, h2, y, hy, hyl, hyx⟩ := h
  refine ⟨?_, ?_, o • y, (W.NΔ T).smul_mem o hy, ?_, ?_⟩
  · unfold InLet at h1 ⊢
    rw [smul_comm, h1]
  · intro δ hδ
    rw [map_smul, h2 δ hδ]
  · rw [smul_comm, hyl]
  · rw [map_smul, ← smul_sub, hyx, smul_comm]

theorem InI_sum {c : ZMod n} {ι : Type} (s : Finset ι) (x : ι → W.DD T) (h : ∀ i ∈ s, InI W T c (x i)) :
    InI W T c (∑ i ∈ s, x i) := by
  classical
  have hadd : ∀ x y, InI W T c x → InI W T c y → InI W T c (x + y) := by
    rintro x y ⟨hx1, hx2, u, hu, hul, hux⟩ ⟨hy1, hy2, u', hu', hul', hux'⟩
    refine ⟨?_, ?_, u + u', (W.NΔ T).add_mem hu hu', ?_, ?_⟩
    · unfold InLet at hx1 hy1 ⊢
      rw [smul_add, hx1, hy1]
    · intro δ hδ
      rw [map_add, hx2 δ hδ, hy2 δ hδ]
    · rw [smul_add, hul, hul']
    · rw [map_add, add_sub_add_comm, hux, hux', smul_add]
  have hzero : InI W T c 0 := ⟨by unfold InLet; rw [smul_zero], fun δ _ => map_zero _, 0,
    (W.NΔ T).zero_mem, smul_zero _, by rw [map_zero, sub_zero, smul_zero]⟩
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hzero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hadd _ _ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem InI_iter (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {w : W.DD T} (h : InI W T c w) (i : ℕ) :
    InI W T c ((W.γ T)^[i] w) := by
  induction i with
  | zero => simpa using h
  | succ i ih => rw [Function.iterate_succ_apply']; exact InI_γ W hT hP2 hpi0 ih

theorem aeval_eq (P : Polynomial O) (x : W.DD T) :
    Polynomial.aeval (W.γ T) P x = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • (W.γ T)^[i] x := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  simp [Module.End.pow_apply]

theorem aevalE_eq (P : Polynomial O) (f : W.EE) :
    Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P f =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • (W.γE W.gam)^[i] f := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  simp [Module.End.pow_apply]

theorem InI_aeval (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {w : W.DD T} (h : InI W T c w)
    (P : Polynomial O) : InI W T c (Polynomial.aeval (W.γ T) P w) := by
  rw [aeval_eq]
  exact InI_sum W _ _ fun i _ => InI_smulO W _ (InI_iter W hT hP2 hpi0 h i)

end Formalism.MainNotions.N.Ln17.PCutBoundRep
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsUnitOfResidueConstNeZero
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup PowerSeries

section PS

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {l : ℕ} [Fact l.Prime]

def residueConst : O⟦X⟧ →+* IsLocalRing.ResidueField O :=
  (IsLocalRing.residue O).comp (PowerSeries.constantCoeff (R := O))

theorem residueConst_apply (f : O⟦X⟧) :
    residueConst f = IsLocalRing.residue O (PowerSeries.constantCoeff f) := rfl

theorem residueConst_X_eq_zero : residueConst (X : O⟦X⟧) = 0 := by
  rw [residueConst_apply]
  simp

theorem residueConst_phi_eq (P : PhiData O l) (f : O⟦X⟧) : residueConst (P.φ f) = residueConst f := by
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hCa : ∀ a : O, P.φ (C a) = C a := by
    intro a
    first
    | exact P.φ.commutes a
    | simpa using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply'] using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply] using P.φ.commutes a
  have hX : residueConst (P.φ X) = 0 := by
    have h6 : P.φ (X - C (l : O)) = P.u * (X - C (l : O)) * X ^ (l - 1) := P.6
    rw [map_sub, hCa] at h6
    have h6' : P.φ X = P.u * (X - C (l : O)) * X ^ (l - 1) + C (l : O) := by rw [← h6]; ring
    rw [h6', map_add, map_mul, map_pow, residueConst_X_eq_zero, zero_pow (by omega), mul_zero, zero_add,
      residueConst_apply, PowerSeries.constantCoeff_C]
    exact (IsLocalRing.residue_eq_zero_iff _).2 P.4
  conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const f]
  rw [map_add, map_mul, map_add, map_mul, hX, mul_zero, zero_add, hCa]
  rw [residueConst_apply, residueConst_apply, PowerSeries.constantCoeff_C]

theorem residueConst_p1_eq_zero (P : PhiData O l) : residueConst (P.p 1) = 0 := by
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hCa : ∀ a : O, P.φ (C a) = C a := by
    intro a
    first
    | exact P.φ.commutes a
    | simpa using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply'] using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply] using P.φ.commutes a
  unfold PhiData.p
  rw [Function.iterate_one]
  have h6 : P.φ (X - C (l : O)) = P.u * (X - C (l : O)) * X ^ (l - 1) := P.6
  rw [map_sub, hCa] at h6
  have h6' : P.φ X = P.u * (X - C (l : O)) * X ^ (l - 1) + C (l : O) := by rw [← h6]; ring
  rw [h6', map_add, map_mul, map_pow, residueConst_X_eq_zero, zero_pow (by omega), mul_zero, zero_add,
    residueConst_apply, PowerSeries.constantCoeff_C]
  exact (IsLocalRing.residue_eq_zero_iff _).2 P.4

theorem level_poly_decomposition (P : PhiData O l) (s : ℕ) (hs : 1 ≤ s) :
    ∃ e h : O⟦X⟧, P.p s = C (l : O) * e + X ^ l * h ∧ residueConst e ≠ 0 := by
  unfold PhiData.p
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hCa : ∀ a : O, P.φ (C a) = C a := by
    intro a
    first
    | exact P.φ.commutes a
    | simpa using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply'] using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply] using P.φ.commutes a
  have hκC : residueConst (C (l : O)) = 0 := by
    rw [residueConst_apply, PowerSeries.constantCoeff_C]
    exact (IsLocalRing.residue_eq_zero_iff _).2 P.4
  have hκXl : residueConst ((X : O⟦X⟧) ^ l) = 0 := by
    rw [map_pow, residueConst_X_eq_zero, zero_pow (by omega)]
  have hmul : ∀ a b a' b' : O⟦X⟧, ∃ a'' b'' : O⟦X⟧,
      (C (l : O) * a + X ^ l * b) * (C (l : O) * a' + X ^ l * b') = C (l : O) * a'' + X ^ l * b'' ∧
      residueConst a'' = 0 := by
    intro a b a' b'
    refine ⟨a * C (l : O) * a' + a * X ^ l * b' + X ^ l * b * a', X ^ l * b * b', by ring, ?_⟩
    simp only [map_add, map_mul, hκC, hκXl, mul_zero, zero_mul, add_zero]
  have hpow : ∀ a b : O⟦X⟧, ∀ m, 2 ≤ m → ∃ a' b' : O⟦X⟧,
      (C (l : O) * a + X ^ l * b) ^ m = C (l : O) * a' + X ^ l * b' ∧ residueConst a' = 0 := by
    intro a b m hm
    induction m, hm using Nat.le_induction with
    | base => rw [pow_two]; exact hmul a b a b
    | succ m hm ih =>
      obtain ⟨a', b', he, hk⟩ := ih
      obtain ⟨a'', b'', he', hk'⟩ := hmul a' b' a b
      exact ⟨a'', b'', by rw [pow_succ, he, he'], hk'⟩
  have hXl : (X : O⟦X⟧) ^ l = X * X ^ (l - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h6 : P.φ (X - C (l : O)) = P.u * (X - C (l : O)) * X ^ (l - 1) := P.6
  rw [map_sub, hCa] at h6
  have hφX : P.φ X = C (l : O) * (1 - P.u * X ^ (l - 1)) + X ^ l * P.u := by
    have h6' : P.φ X = P.u * (X - C (l : O)) * X ^ (l - 1) + C (l : O) := by rw [← h6]; ring
    rw [h6', hXl]
    ring
  induction s, hs using Nat.le_induction with
  | base =>
    refine ⟨1 - P.u * X ^ (l - 1), P.u, by rw [Function.iterate_one, hφX], ?_⟩
    rw [map_sub, map_one, map_mul, map_pow, residueConst_X_eq_zero, zero_pow (by omega), mul_zero, sub_zero]
    exact one_ne_zero
  | succ s hs ih =>
    obtain ⟨e, h, he, hk⟩ := ih
    obtain ⟨a', b', hab, hka⟩ := hpow (1 - P.u * X ^ (l - 1)) P.u l hl2
    refine ⟨P.φ e + a' * P.φ h, b' * P.φ h, ?_, ?_⟩
    · rw [Function.iterate_succ_apply', he, map_add, map_mul, map_mul, hCa, map_pow, hφX, hab]
      ring
    · rw [map_add, map_mul, hka, zero_mul, add_zero, residueConst_phi_eq]
      exact hk

theorem isUnit_of_residueConst_ne_zero {e : O⟦X⟧} (hκ : residueConst e ≠ 0) : IsUnit e := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [residueConst_apply] at hκ
  by_contra h
  exact hκ ((IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h))

theorem l_pow_mem_span_level_X_pow (P : PhiData O l) (s : ℕ) (hs : 1 ≤ s) (B : ℕ) :
    ∃ a b : O⟦X⟧, C (l : O) ^ B = a * P.p s + b * X ^ B := by
  obtain ⟨e, h, hp, he⟩ := level_poly_decomposition P s hs
  obtain ⟨u, hu⟩ := isUnit_of_residueConst_ne_zero he
  obtain ⟨k, hk⟩ := sub_dvd_pow_sub_pow (C (l : O) * e) (-(X ^ l * h)) B
  rw [sub_neg_eq_add, ← hp] at hk
  have hl : B ≤ l * B := Nat.le_mul_of_pos_left B (Fact.out : l.Prime).pos
  refine ⟨k * (↑u⁻¹ : O⟦X⟧) ^ B, X ^ (l * B - B) * (-h) ^ B * (↑u⁻¹ : O⟦X⟧) ^ B, ?_⟩
  have hy : (-(X ^ l * h) : O⟦X⟧) ^ B = X ^ (l * B - B) * (-h) ^ B * X ^ B := by
    rw [mul_assoc, mul_comm ((-h) ^ B), ← mul_assoc, ← pow_add, Nat.sub_add_cancel hl, pow_mul,
      ← mul_pow, neg_mul_eq_mul_neg]
  have hue : (C (l : O) * e) ^ B * (↑u⁻¹ : O⟦X⟧) ^ B = C (l : O) ^ B := by
    rw [← mul_pow, mul_assoc, ← hu, Units.mul_inv, mul_one]
  calc C (l : O) ^ B = (C (l : O) * e) ^ B * (↑u⁻¹ : O⟦X⟧) ^ B := hue.symm
    _ = (P.p s * k + (-(X ^ l * h)) ^ B) * (↑u⁻¹ : O⟦X⟧) ^ B := by rw [← hk, sub_add_cancel]
    _ = _ := by rw [hy]; ring

end PS

section Bridge

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem powerSeriesConst_add {W : LocWach PD LL O v n} (Br : PhiBridge W) (F F' : PowerSeries O) :
    Br.cst (F + F') = Br.cst F + Br.cst F' := by
  unfold PhiBridge.cst
  funext x
  first
  | exact map_add Br.ι F F'
  | exact Br.ι.map_add F F'
  | simp

theorem l_pow_mem_levels_q_pow_ideal {W : LocWach PD LL O v n} (Br : PhiBridge W) (Bq : ℕ) {g : LetA O n}
    (hg : g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}) :
    g ∈ W.AΔ ∧ ∃ N : ℕ, ∃ a ∈ W.AΔ, ∃ b ∈ W.AΔ, lA W ^ N = a * g + b * qA W ^ Bq := by
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  have key : ∃ F : PowerSeries O, g = Br.cst F ∧
      ∃ N : ℕ, ∃ a b : PowerSeries O, C ((PD.p : ℕ) : O) ^ N = a * F + b * X ^ Bq := by
    induction hg using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨a, b, hab⟩ := l_pow_mem_span_level_X_pow Br.P k hk Bq
      exact ⟨Br.P.p k, Br.ps_eq k, Bq, a, b, hab⟩
    | one =>
      exact ⟨1, Br.cst_one.symm, 0, 1, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨F₁, rfl, N₁, a₁, b₁, h₁⟩ := hx
      obtain ⟨F₂, rfl, N₂, a₂, b₂, h₂⟩ := hy
      refine ⟨F₁ * F₂, (Br.cst_mul F₁ F₂).symm, N₁ + N₂, a₁ * a₂,
        b₁ * a₂ * F₂ + a₁ * F₁ * b₂ + b₁ * b₂ * X ^ Bq, ?_⟩
      rw [pow_add, h₁, h₂]
      ring
  obtain ⟨F, rfl, N, a, b, h⟩ := key
  refine ⟨Br.cst_mem F, N, Br.cst a, Br.cst_mem a, Br.cst b, Br.cst_mem b, ?_⟩
  rw [Br.lA_eq, Br.qA_eq, ← Br.cst_pow, ← Br.cst_pow, ← Br.cst_mul, ← Br.cst_mul,
    ← powerSeriesConst_add, h]

end Bridge

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

