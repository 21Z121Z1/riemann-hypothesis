import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0001

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.PhiItSmul
section
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Model

variable {O : Type} [CommRing O] {Bs : Formalism.ExponentWindows.E.Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

def PsM (Bs : Formalism.ExponentWindows.E.Base O) : Submonoid (PowerSeries O) := Submonoid.closure (Set.range Bs.p)

theorem p_mem (s : ℕ) : Bs.p s ∈ PsM Bs := Submonoid.subset_closure ⟨s, rfl⟩

theorem q_mem : Bs.q ∈ PsM Bs := p_mem (Bs := Bs) 0

theorem φ_p (s : ℕ) : Bs.φ (Bs.p s) = Bs.p (s + 1) := by
  rw [Formalism.ExponentWindows.E.Base.p, Formalism.ExponentWindows.E.Base.p, Function.iterate_succ_apply']

theorem φ_mem {f : PowerSeries O} (hf : f ∈ PsM Bs) : Bs.φ f ∈ PsM Bs := by
  induction hf using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [φ_p]
    exact p_mem _
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem φit_mem (k : ℕ) {f : PowerSeries O} (hf : f ∈ PsM Bs) : (⇑Bs.φ)^[k] f ∈ PsM Bs := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact φ_mem ih

theorem Lam_mem (H : ℕ → ℕ) (ell : ℕ) : Formalism.ExponentWindows.abelian₂ Bs.p H ell ∈ PsM Bs :=
  Submonoid.prod_mem _ fun s _ => pow_mem (p_mem s) _

variable (L : Formalism.ExponentWindows.E.Lat Bs n V)

theorem phiIt_smul' (i : ZMod n) (k : ℕ) (a : PowerSeries O) (x : V) :
    L.phiIt i k (a • x) = (⇑Bs.φ)^[k] a • L.phiIt i k x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Formalism.ExponentWindows.E.Lat.phiIt, ih, L.φ_semi, Function.iterate_succ_apply']
    rfl

theorem phiIt_N (hh : ℕ) (h5 : ∀ i, L.P5M i hh) (k : ℕ) :
    ∃ Pr ∈ PsM Bs, ∀ i, ∀ x ∈ L.N i, Pr • L.phiIt i k x ∈ L.N (i + (k : ZMod n)) := by
  induction k with
  | zero =>
    refine ⟨1, one_mem _, fun i x hx => ?_⟩
    rw [one_smul, Nat.cast_zero, add_zero]
    exact hx
  | succ k ih =>
    obtain ⟨Pr, hPr, h⟩ := ih
    refine ⟨Bs.q ^ hh * Bs.φ Pr, mul_mem (pow_mem q_mem _) (φ_mem hPr), fun i x hx => ?_⟩
    rw [Formalism.ExponentWindows.E.Lat.phiIt, mul_smul, ← L.φ_semi]
    apply h5
    have e : i + ((k + 1 : ℕ) : ZMod n) - 1 = i + (k : ZMod n) := by push_cast; ring
    rw [e]
    exact h i x hx

theorem pull_N (hh : ℕ) (h5 : ∀ i, L.P5M i hh) (k : ℕ) :
    ∃ Pr ∈ PsM Bs, ∀ i, ∀ x ∈ L.pull i k, Pr • x ∈ L.N (i + (k : ZMod n)) := by
  obtain ⟨Pr, hPr, h⟩ := phiIt_N L hh h5 k
  refine ⟨Pr, hPr, fun i x hx => ?_⟩
  have : L.pull i k ≤ Formalism.ExponentWindows.E.dv Pr (L.N (i + (k : ZMod n))) := by
    rw [Formalism.ExponentWindows.E.Lat.pull, Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    exact h i u hu
  exact this hx

theorem relay_N (hh : ℕ) (h5 : ∀ i, L.P5M i hh) (c c' : ZMod n) (k j : ℕ)
    (hc : c' + (k : ZMod n) = c) (Λ : PowerSeries O) (hΛ : Λ ∈ PsM Bs) (a : PowerSeries O) (w τ : V)
    (hw : w ∈ Formalism.ExponentWindows.E.dv Λ (L.pull c' k)) (hτ : τ ∈ L.pull c j) :
    ∃ Pr ∈ PsM Bs, Pr • (a • L.phiIt c j w - τ) ∈ L.N (c + (j : ZMod n)) := by
  obtain ⟨Prk, hPrk, hk⟩ := pull_N L hh h5 k
  obtain ⟨Prj, hPrj, hj⟩ := phiIt_N L hh h5 j
  obtain ⟨Prj', hPrj', hj'⟩ := pull_N L hh h5 j
  have h1 : (Prk * Λ) • w ∈ L.N c := by
    rw [mul_smul, ← hc]
    exact hk c' _ hw
  have h2 := hj c _ h1
  rw [phiIt_smul'] at h2
  have h3 := hj' c τ hτ
  refine ⟨Prj' * (Prj * (⇑Bs.φ)^[j] (Prk * Λ)),
    mul_mem hPrj' (mul_mem hPrj (φit_mem j (mul_mem hPrk hΛ))), ?_⟩
  rw [smul_sub]
  refine Submodule.sub_mem _ ?_ ?_
  · have : (Prj' * (Prj * (⇑Bs.φ)^[j] (Prk * Λ))) • a • L.phiIt c j w =
        (Prj' * a) • Prj • (⇑Bs.φ)^[j] (Prk * Λ) • L.phiIt c j w := by
      simp only [smul_smul]
      congr 1
      ring
    rw [this]
    exact Submodule.smul_mem _ _ h2
  · have : (Prj' * (Prj * (⇑Bs.φ)^[j] (Prk * Λ))) • τ = (Prj * (⇑Bs.φ)^[j] (Prk * Λ)) • Prj' • τ := by
      simp only [smul_smul]
      congr 1
      ring
    rw [this]
    exact Submodule.smul_mem _ _ h3

end Model

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {I : BaseId W} {T : LocLat G Qp LL O}

theorem prod_pad {R : Type} [CommMonoid R] (F : ℕ → R) (k : ℕ → ℕ) {m m' : ℕ} (h : m ≤ m') :
    ∏ s ∈ Finset.range m', F s ^ (if s < m then k s else 0) = ∏ s ∈ Finset.range m, F s ^ k s := by
  rw [← Finset.prod_subset (Finset.range_subset_range.2 h)]
  · exact Finset.prod_congr rfl fun s hs => by rw [if_pos (Finset.mem_range.1 hs)]
  · intro s _ hs
    rw [if_neg (fun h' => hs (Finset.mem_range.2 h')), pow_zero]

theorem isPs_one : IsPs W (1 : LetA O n) := ⟨fun _ => 0, 0, by simp⟩

theorem isPs_pS (s : ℕ) : IsPs W (pS W s) := by
  refine ⟨fun t => if t = s then 1 else 0, s + 1, ?_⟩
  rw [Finset.prod_eq_single s]
  · simp
  · intro t _ ht; simp [ht]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self s)) h

theorem isPs_mul {f g : LetA O n} (hf : IsPs W f) (hg : IsPs W g) : IsPs W (f * g) := by
  obtain ⟨k, m, rfl⟩ := hf
  obtain ⟨k', m', rfl⟩ := hg
  refine ⟨fun s => (if s < m then k s else 0) + (if s < m' then k' s else 0), m + m', ?_⟩
  simp only [pow_add, Finset.prod_mul_distrib]
  rw [prod_pad _ k (Nat.le_add_right m m'), prod_pad _ k' (Nat.le_add_left m' m)]

theorem isPs_d {f : PowerSeries O} (hf : f ∈ PsM I.Bs) : IsPs W (I.d f) := by
  induction hf using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [I.d_p]
    exact isPs_pS s
  | one => rw [map_one]; exact isPs_one
  | mul x y _ _ hx hy => rw [map_mul]; exact isPs_mul hx hy

theorem d_smul_NΔ (f : PowerSeries O) {x : W.DD T} (hx : x ∈ W.NΔ T) : I.d f • x ∈ W.NΔ T :=
  ⟨(W.N T).smul_mem _ hx.1, fun δ hδ => by rw [γD_smulA, I.γA_Δ δ hδ, hx.2 δ hδ]⟩

theorem tot_NΔ (C : Coord W I T) (x : ZMod n → C.V) (hx : ∀ i, x i ∈ (latOf C).N i) :
    tot C x ∈ W.NΔ T :=
  ⟨(W.N T).sum_mem fun i _ => hx i, fun δ hδ => tot_Δ C x δ hδ⟩

theorem tot_single (C : Coord W I T) (k : ZMod n) (x : C.V) : tot C (Pi.single k x) = C.t k x := by
  rw [tot, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, C.t_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem tot_sm (C : Coord W I T) (M : ℕ) (z : ZMod n → C.V)
    (hz : ∀ i, z i ∈ Formalism.ExponentWindows.E.sm (PowerSeries.X ^ M) ((latOf C).N i)) :
    tot C z ∈ mulSet W T (W.π₀ ^ M) (W.NΔ T) := by
  have h : ∀ i, ∃ x ∈ (latOf C).N i, (PowerSeries.X ^ M : PowerSeries O) • x = z i := fun i => hz i
  choose x hx hxz using h
  refine ⟨tot C x, tot_NΔ C x hx, ?_⟩
  have : z = (PowerSeries.X ^ M : PowerSeries O) • x := by
    funext i
    exact (hxz i).symm
  rw [this, tot_smul, map_pow, I.d_X]

theorem rho_of (hF1 : F1 W) (hF2 : F2 W) (hcr : IsCrys PD T.ρ) (hh M : ℕ)
    (hJ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T.ρ τ (Set.Icc (-(hh : ℤ)) hh))
    (hM : hh < (PD.p - 1) * M) (C : Coord W I T) (h5 : ∀ i, (latOf C).P5M i hh)
    (c c' : ZMod n) (k : ℕ) (hc : c' + (k : ZMod n) = c) (Λ : PowerSeries O) (hΛ : Λ ∈ PsM I.Bs)
    (w : C.V) (hw : w ∈ Formalism.ExponentWindows.E.dv Λ ((latOf C).pull c' k)) (j g sig : ℕ) (y z : ZMod n → C.V)
    (hρ : (latOf C).IsRho c j M g sig w y z) : (y, z) ∈ Zf C := by
  obtain ⟨τ, ⟨hτ, -⟩, hy, hcoc, hz⟩ := hρ
  have hZ : (tot C y, tot C z) ∈ W.wachCocyclesDelta T := (cocycle_iff C y z).1 hcoc
  have hzM := tot_sm C M z hz
  have hyt : tot C y = C.t (c + (j : ZMod n)) (I.Bs.lc ^ sig • (latOf C).phiIt c j w - τ) := by
    rw [hy, tot_single]
  refine (mem_Zf C _).2 ⟨⟨_, hZ⟩, ?_, rfl⟩
  refine hF2 hh M hM T hcr hJ (c + (j : ZMod n)) ⟨_, hZ⟩ ⟨?_, ?_, hzM⟩ ?_
  · change (letE (c + (j : ZMod n)) : LetA O n) • tot C y = tot C y
    rw [hyt]
    exact C.t_letter _ _
  · change W.γD T W.gamK (tot C y) - tot C y ∈ mulSet W T (W.π₀ ^ M) (W.NΔ T)
    rw [((mem_Z1DΔ _ _).1 hZ).1]
    obtain ⟨x, hx, hxz⟩ := hzM
    obtain ⟨x', hx', hφ⟩ := ((hF1 hh M hM).1 T hcr hJ).1 x hx
    refine ⟨I.d I.Bs.q • x' - x, (W.NΔ T).sub_mem (d_smul_NΔ _ hx') hx, ?_⟩
    rw [hxz, hφ, smul_sub, I.d_q, mul_smul]
  · obtain ⟨Pr, hPr, hN⟩ := relay_N (latOf C) hh h5 c c' k j hc Λ hΛ (I.Bs.lc ^ sig) w τ hw hτ
    refine ⟨I.d Pr, isPs_d hPr, ?_⟩
    change I.d Pr • tot C y ∈ W.NΔ T
    rw [hyt, ← C.t_smul]
    exact ⟨hN, fun δ hδ => C.t_Δ _ _ δ hδ⟩

theorem rho_field (hF1 : F1 W) (hF2 : F2 W) (hcr : IsCrys PD T.ρ) (hh : ℕ)
    (hJ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T.ρ τ (Set.Icc (-(hh : ℤ)) hh)) (hp : 2 ≤ PD.p)
    (C : Coord W I T) (h5 : ∀ i, (latOf C).P5M i hh) (Cu : Formalism.ExponentWindows.E.Cuts n) (H : ZMod n → ℕ → ℕ)
    (j g sig : ℕ) :
    ∀ c ∈ Cu.cuts, ∀ w, (latOf C).Wc Cu (Formalism.ExponentWindows.E.LamOf I.Bs Cu H) c w →
      ∀ y z, (latOf C).IsRho c j (Formalism.ExponentWindows.E.parM I.Bs.ℓ hh g) g sig w y z → (y, z) ∈ Zf C := by
  intro c _ w hw y z hρ
  refine rho_of hF1 hF2 hcr hh _ hJ ?_ C h5 c (c - (Cu.ell c : ZMod n)) (Cu.ell c) (sub_add_cancel _ _)
    _ (Lam_mem (H c) (Cu.ell c)) w hw.2 j g sig y z hρ
  rw [Formalism.ExponentWindows.E.parM, I.ℓ_eq]
  have := Nat.lt_mul_div_succ (hh + 2 * g) (show 0 < PD.p - 1 by omega)
  omega

end Formalism.MainNotions.WachCoordinates.Br
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.XDvdLevCQ
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LevW

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.Ring

section

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def levC (i : ZMod n) (ζ : LL) : PowerSeries O →ₐ[O] PowerSeries LL :=
  (W.lev i ζ).comp (Pi.constAlgHom O (ZMod n) (PowerSeries O))

theorem lev_eq_levC (i : ZMod n) (ζ : LL) (a : LetA O n) : W.lev i ζ a = levC W i ζ (a i) := by
  have h := W.lev_letter i ζ (a - Pi.constAlgHom O (ZMod n) (PowerSeries O) (a i)) (by simp)
  rw [map_sub, sub_eq_zero] at h
  exact h

theorem levC_X (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ E : PowerSeries LL, PowerSeries.constantCoeff E = 1 ∧ PowerSeries.derivative LL E = E ∧
      levC W i ζ PowerSeries.X = PowerSeries.C ζ * E - 1 := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π i ζ ⟨1, by rwa [pow_one]⟩
  refine ⟨E, h0, h1, ?_⟩
  have h3 : levC W i ζ PowerSeries.X = W.lev i ζ letπ := by
    first
    | rfl
    | exact (lev_eq_levC W i ζ letπ).symm
  rw [h3]
  linear_combination h2

private theorem coeff_zero_derivative_eq_coeff_one {R : Type} [CommRing R] (f : PowerSeries R) :
    PowerSeries.coeff 0 (PowerSeries.derivative R f) = PowerSeries.coeff 1 f := by
  first
  | (rw [show PowerSeries.derivative R f = f.derivativeFun from rfl, PowerSeries.coeff_derivativeFun]; simp)
  | simp [PowerSeries.coeff_derivativeFun]
  | simp [PowerSeries.derivative, PowerSeries.coeff_derivativeFun]

theorem X_dvd_levC_q (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) (hp : 2 ≤ PD.p) :
    PowerSeries.X ∣ levC W i ζ W.q₀ := by
  obtain ⟨E, hE0, _, hX⟩ := levC_X W i ζ hζ
  have h := congrArg (levC W i ζ) W.q₀_def
  simp only [map_mul, map_sub, map_pow, map_add, map_one, hX] at h
  have h2 := congrArg PowerSeries.constantCoeff h
  simp only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.constantCoeff_C, hE0] at h2
  rw [PowerSeries.X_dvd_iff]
  have h3 : (ζ - 1) * PowerSeries.constantCoeff (levC W i ζ W.q₀) = 0 := by
    linear_combination h2 + hζ.pow_eq_one
  have hne : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one (by omega))
  exact (mul_eq_zero.mp h3).resolve_left hne

end

section Div

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem residue_q₀ [IsLocalRing O] (hp : PD.p.Prime) (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) :
    PowerSeries.map (IsLocalRing.residue O) W.q₀ = PowerSeries.X ^ (PD.p - 1) := by
  haveI := Fact.mk hp
  have hk : ((PD.p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hpm
  have hK : ((PD.p : ℕ) : PowerSeries (IsLocalRing.ResidueField O)) = 0 := by
    rw [← map_natCast (PowerSeries.C (R := IsLocalRing.ResidueField O)), hk, map_zero]
  haveI : CharP (PowerSeries (IsLocalRing.ResidueField O)) PD.p := by
    first
    | exact (CharP.charP_iff_prime_eq_zero hp).mpr hK
    | exact (charP_iff_prime_eq_zero hp).mpr hK
  have h := congrArg (PowerSeries.map (IsLocalRing.residue O)) W.q₀_def
  simp only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X] at h
  rw [add_pow_char, one_pow, add_sub_cancel_left] at h
  have h2 : PowerSeries.X * PowerSeries.map (IsLocalRing.residue O) W.q₀ =
      PowerSeries.X * PowerSeries.X ^ (PD.p - 1) := by
    rw [h, ← pow_succ', Nat.sub_add_cancel hp.one_le]
  exact mul_left_cancel₀ PowerSeries.X_ne_zero h2

private theorem eq_of_mul_mul_eq_of_det_ne_zero (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) (hp : 2 ≤ PD.p)
    (hpL : ((PD.p : ℕ) : LL) ≠ 0) (b : ℕ) (c : PowerSeries O)
    (h : PowerSeries.X ^ (b + 1) ∣ levC W i ζ (W.q₀ * c)) : PowerSeries.X ^ b ∣ levC W i ζ c := by
  obtain ⟨E, hE0, hE1, hX⟩ := levC_X W i ζ hζ
  obtain ⟨w, hw⟩ := X_dvd_levC_q W i ζ hζ hp
  have h1 := congrArg (levC W i ζ) W.q₀_def
  simp only [map_mul, map_sub, map_pow, map_add, map_one, hX, hw] at h1
  have e : (PowerSeries.C ζ * E) ^ PD.p = E ^ PD.p := by
    first
    | rw [mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul]
    | simp [mul_pow, ← map_pow, hζ.pow_eq_one]
  have h1' : (PowerSeries.C ζ * E - 1) * w * PowerSeries.X = E ^ PD.p - 1 := by
    rw [← e]
    linear_combination h1
  have hc : PowerSeries.coeff 0 ((PowerSeries.C ζ * E - 1) * w) =
      PowerSeries.coeff 1 (E ^ PD.p - 1) := by
    rw [← h1', PowerSeries.coeff_succ_mul_X]
  have hD : PowerSeries.coeff 1 (E ^ PD.p) = ((PD.p : ℕ) : LL) := by
    rw [← coeff_zero_derivative_eq_coeff_one, Derivation.leibniz_pow, hE1]
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hE0]
  have hcw : PowerSeries.constantCoeff w ≠ 0 := by
    intro h0
    apply hpL
    have e2 : PowerSeries.coeff 1 (E ^ PD.p - 1) = PowerSeries.coeff 1 (E ^ PD.p) := by
      first
      | simp
      | simp [PowerSeries.coeff_one]
    rw [← hD, ← e2, ← hc, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, h0, mul_zero]
  have hwU : IsUnit w := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    exact isUnit_iff_ne_zero.mpr hcw
  rw [map_mul, hw, pow_succ', mul_assoc] at h
  have h2 := (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).mp h
  first
  | exact hwU.dvd_mul_left.mp h2
  | exact (IsUnit.dvd_mul_left hwU).mp h2
  | exact (Units.dvd_mul_left (u := hwU.unit)).mp h2

private theorem q0_dvd_of_X_dvd_levC_primitive_roots [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hp : PD.p.Prime) (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hinj : Function.Injective (algebraMap O LL)) {ζ₀ : LL} (hζ₀ : IsPrimitiveRoot ζ₀ PD.p)
    (i : ZMod n) (a : PowerSeries O)
    (hv : ∀ ζ : LL, IsPrimitiveRoot ζ PD.p → PowerSeries.X ∣ levC W i ζ a) : W.q₀ ∣ a := by
  classical
  have hres := residue_q₀ W hp hpm
  have hne : PowerSeries.map (IsLocalRing.residue O) W.q₀ ≠ 0 := by
    rw [hres]
    exact pow_ne_zero _ PowerSeries.X_ne_zero
  obtain ⟨q, r, hdeg0, heq⟩ : ∃ (q : PowerSeries O) (r : Polynomial O),
      r.degree < ((PowerSeries.map (IsLocalRing.residue O) W.q₀).order.toNat : WithBot ℕ) ∧
      a = W.q₀ * q + (r : PowerSeries O) := by
    first
    | (obtain ⟨q, r, hr⟩ := PowerSeries.exists_isWeierstrassDivision (f := a) hne
       exact ⟨q, r, hr.degree_lt, hr.eq_mul_add⟩)
    | (obtain ⟨q, r, hr⟩ := PowerSeries.exists_isWeierstrassDivision a hne
       exact ⟨q, r, hr.degree_lt, hr.eq_mul_add⟩)
    | exact ⟨_, _, (PowerSeries.isWeierstrassDivision_weierstrassDiv_weierstrassMod a hne).degree_lt,
        (PowerSeries.isWeierstrassDivision_weierstrassDiv_weierstrassMod a hne).eq_mul_add⟩
  rw [hres, PowerSeries.order_X_pow] at hdeg0
  have hdeg : r.degree < ((PD.p - 1 : ℕ) : WithBot ℕ) := by
    first
    | (rw [ENat.toNat_coe] at hdeg0; exact hdeg0)
    | exact hdeg0
    | simpa only [ENat.toNat_coe] using hdeg0
  have hroots : ∀ ζ ∈ primitiveRoots PD.p LL, (r.map (algebraMap O LL)).eval (ζ - 1) = 0 := by
    intro ζ hζm
    have hζ : IsPrimitiveRoot ζ PD.p := (mem_primitiveRoots hp.pos).mp hζm
    obtain ⟨E, hE0, _, hX⟩ := levC_X W i ζ hζ
    have hC : ∀ c : O, levC W i ζ (PowerSeries.C c) = PowerSeries.C (algebraMap O LL c) := by
      intro c
      have hc := (levC W i ζ).commutes c
      first
      | simpa [PowerSeries.algebraMap_apply] using hc
      | simpa [PowerSeries.algebraMap_apply'] using hc
    have key : ∀ s : Polynomial O, PowerSeries.constantCoeff (levC W i ζ (s : PowerSeries O)) =
        (s.map (algebraMap O LL)).eval (ζ - 1) := by
      intro s
      refine Polynomial.induction_on s ?_ ?_ ?_
      · intro c
        simp [hC]
      · intro p1 p2 h1 h2
        simp [h1, h2]
      · intro k c _
        simp [hC, hX, hE0]
    have h1 := hv ζ hζ
    rw [heq, map_add, map_mul] at h1
    have h3 := dvd_mul_of_dvd_left (X_dvd_levC_q W i ζ hζ hp.two_le) (levC W i ζ q)
    have h2 := (dvd_add_right h3).mp h1
    rw [PowerSeries.X_dvd_iff, key] at h2
    exact h2
  have hR0 : r.map (algebraMap O LL) = 0 := by
    by_contra hR
    have hRdeg : (r.map (algebraMap O LL)).degree < ((PD.p - 1 : ℕ) : WithBot ℕ) := by
      first
      | exact lt_of_le_of_lt Polynomial.degree_map_le hdeg
      | exact lt_of_le_of_lt (Polynomial.degree_map_le _ _) hdeg
    have hnd : (r.map (algebraMap O LL)).natDegree < PD.p - 1 :=
      (Polynomial.natDegree_lt_iff_degree_lt hR).mpr hRdeg
    apply hR
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
      ((primitiveRoots PD.p LL).image (fun z => z - 1))
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact hroots z hz
    · rw [Finset.card_image_of_injective _ (sub_left_injective), hζ₀.card_primitiveRoots,
        Nat.totient_prime hp]
      exact hnd
  have hr0 : r = 0 := by
    apply Polynomial.map_injective (algebraMap O LL) hinj
    rw [hR0, Polynomial.map_zero]
  exact ⟨q, by rw [heq, hr0, Polynomial.coe_zero, add_zero]⟩

theorem q_pow_dvd [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hp : PD.p.Prime) (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hinj : Function.Injective (algebraMap O LL)) {ζ₀ : LL} (hζ₀ : IsPrimitiveRoot ζ₀ PD.p)
    (i : ZMod n) (b : ℕ) (a : PowerSeries O)
    (hv : ∀ ζ : LL, IsPrimitiveRoot ζ PD.p → PowerSeries.X ^ b ∣ levC W i ζ a) :
    ∃ h : PowerSeries O, a = W.q₀ ^ b * h := by
  have hp2 : 2 ≤ PD.p := hp.two_le
  have hpL : ((PD.p : ℕ) : LL) ≠ 0 := by
    intro h0
    have h1 := W.v_l
    rw [h0, AddValuation.map_zero] at h1
    first
    | exact WithTop.top_ne_one h1
    | exact absurd h1 (by simp)
    | simp at h1
  induction b generalizing a with
  | zero => exact ⟨a, by simp⟩
  | succ b ih =>
    obtain ⟨c, rfl⟩ := q0_dvd_of_X_dvd_levC_primitive_roots W hp hpm hinj hζ₀ i a
      (fun ζ hζ => dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero b)) (hv ζ hζ))
    obtain ⟨h, hh⟩ := ih c (fun ζ hζ => eq_of_mul_mul_eq_of_det_ne_zero W i ζ hζ hp2 hpL b c (hv ζ hζ))
    exact ⟨h, by rw [hh]; ring⟩

end Div

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LevW
end
end

