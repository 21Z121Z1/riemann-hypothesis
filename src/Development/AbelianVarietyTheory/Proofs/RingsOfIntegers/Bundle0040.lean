import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0037
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0015
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AddCharMemValuationSubring
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SectionRegularOnModelOfNuNonneg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0038

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnits
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.LatticeIndex

namespace GlobalTheory.TrivLattice

private theorem isAddTorsion_quotient_of_nsmul_mem {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (m : ℕ) (hm : m ≠ 0)
    (h : ∀ b ∈ B, m • b ∈ A) : IsAddTorsion (B ⧸ A.addSubgroupOf B) := by
  intro x
  refine QuotientAddGroup.induction_on x (fun b => ?_)
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, Nat.pos_of_ne_zero hm, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  simpa using h b b.2

theorem relIndex_ne_zero_of_fg {G : Type} [AddCommGroup G] (A B : AddSubgroup G) [AddGroup.FG B] (m : ℕ) (hm : m ≠ 0)
    (h : ∀ b ∈ B, m • b ∈ A) : A.relIndex B ≠ 0 := by
  haveI : AddGroup.FG (B ⧸ A.addSubgroupOf B) :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective (A.addSubgroupOf B))
  haveI := AddCommGroup.finite_of_fg_isAddTorsion _ (isAddTorsion_quotient_of_nsmul_mem A B m hm h)
  exact AddSubgroup.index_ne_zero_of_finite

section
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem nsmul_mem_of_le {A B : Submodule (𝓞 E) (Fin n → E)} {k : ℕ} (h : Ideal.span {(k : 𝓞 E)} • A ≤ B)
    {v : Fin n → E} (hv : v ∈ A) : k • v ∈ B := by
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact h (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hv)

theorem fg_of_nsmul_mem (A : Submodule (𝓞 E) (Fin n → E)) {k : ℕ} (hk : k ≠ 0) (h : ∀ v ∈ A, k • v ∈ stdLat E n) :
    AddGroup.FG A.toAddSubgroup := by
  let f : (Fin n → E) →ₗ[ℤ] (Fin n → E) := (k : ℤ) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h0 : (k : ℤ) • (x - y) = 0 := by
      simp only [f, LinearMap.smul_apply, LinearMap.id_apply] at hxy
      rw [smul_sub, hxy, sub_self]
    rcases smul_eq_zero.1 h0 with h0 | h0
    · exact absurd (by exact_mod_cast h0) hk
    · exact sub_eq_zero.1 h0
  let T : Submodule ℤ (Fin n → E) := LinearMap.range ((GlobalTheory.LatticeIndex.incl E n).restrictScalars ℤ)
  have hT : T.FG := by
    simp only [T, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  haveI := isNoetherian_of_fg_of_noetherian T hT
  have hle : (A.restrictScalars ℤ).map f ≤ T := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨u, hu⟩ := GlobalTheory.LatticeIndex.mem_std.1 (h v hv)
    refine ⟨u, ?_⟩
    simp only [f, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]
    exact hu
  have hA : (A.restrictScalars ℤ).FG :=
    Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le_of_isNoetherian hle)
  exact (AddGroup.fg_iff_addSubgroup_fg _).2 ((Submodule.fg_iff_addSubgroup_fg _).1 hA)

theorem index_part (Λ : GenLat E n) (N M ℓ k : ℕ) (hL : Λ.LevOK N M) (hl : ℓ.Prime) (hk : Nat.Coprime k ℓ)
    (h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n) (r : ℕ) :
    (Λ.zCard N r).factorization ℓ = (Λ.mIdx N r).factorization ℓ ∧ Λ.mIdx N r ≠ 0 := by
  obtain ⟨hNodd, -, hNle⟩ := hL
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hl.ne_one ((Nat.coprime_zero_left ℓ).1 hk)
  have memLn : ∀ x, x ∈ Λ.Ln ↔ x ∈ Λ.La ∧ x ∈ stdLat E n := fun x => by
    unfold GenLat.Ln
    exact Submodule.mem_inf
  have hS : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup ≤ Λ.Ln.toAddSubgroup := fun x hx => hNle hx
  have hLn : Λ.Ln.toAddSubgroup ≤ Λ.La.toAddSubgroup := fun x hx => ((memLn x).1 hx).1
  haveI := fg_of_nsmul_mem Λ.La hk0 h1
  haveI := fg_of_nsmul_mem Λ.Ln one_ne_zero (fun v hv => by rw [one_smul]; exact ((memLn v).1 hv).2)
  have hkLn : ∀ b ∈ Λ.La.toAddSubgroup, k • b ∈ Λ.Ln.toAddSubgroup := fun b hb =>
    (memLn _).2 ⟨nsmul_mem hb k, h1 b hb⟩
  have ha : Λ.Ln.toAddSubgroup.relIndex Λ.La.toAddSubgroup ≠ 0 :=
    relIndex_ne_zero_of_fg _ _ k hk0 hkLn
  have hnd := GlobalTheory.LatticeIndex.not_dvd_relIndex _ _ k ℓ hl hk ha hkLn
  have hb : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ≠ 0 := by
    refine relIndex_ne_zero_of_fg _ _ N hNodd.pos.ne' (fun b hb => ?_)
    show N • b ∈ Ideal.span {(N : 𝓞 E)} • stdLat E n
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ((memLn b).1 hb).2
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hS hLn
  change ((Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup ^ r).factorization ℓ =
      ((Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ^ r).factorization ℓ ∧
    (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ^ r ≠ 0
  refine ⟨?_, pow_ne_zero _ hb⟩
  rw [← hmul, mul_pow, Nat.factorization_mul (pow_ne_zero _ hb) (pow_ne_zero _ ha)]
  simp [Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnd]

theorem detSet_max {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation E Γ)
    (hw : ∀ r : 𝓞 E, w (algebraMap (𝓞 E) E r) ≤ 1) (A : Submodule (𝓞 E) (Fin n → E)) {k : ℕ} (hk : w (k : E) = 1)
    (h1 : ∀ v ∈ A, k • v ∈ stdLat E n) (h2 : ∀ v ∈ stdLat E n, k • v ∈ A) :
    (∀ y ∈ detSet A, w y ≤ 1) ∧ ∃ y ∈ detSet A, w y = 1 := by
  constructor
  · rintro y ⟨v, hv, rfl⟩
    have hc := GlobalTheory.LatticeIndex.det_cols (m := (1 : Matrix (Fin n) (Fin n) E)) (a := (k : E)) (v := v)
      (u := fun i => k • v i) (fun i => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul])
    obtain ⟨r, hr⟩ := GlobalTheory.LatticeIndex.det_std (u := fun i => k • v i) (fun i => h1 _ (hv i))
    rw [Matrix.det_one, _root_.one_mul, ← hr] at hc
    have hwc := congrArg w hc
    rw [map_mul, map_pow, hk, one_pow, _root_.one_mul] at hwc
    rw [hwc]
    exact hw r
  · refine ⟨(k : E) ^ n, ⟨fun i => k • (Pi.single i 1 : Fin n → E),
      fun i => h2 _ (GlobalTheory.LatticeIndex.single_std i), ?_⟩, ?_⟩
    · have hc := GlobalTheory.LatticeIndex.det_cols (m := (1 : Matrix (Fin n) (Fin n) E)) (a := (k : E))
        (v := fun i => (Pi.single i 1 : Fin n → E)) (u := fun i => k • (Pi.single i 1 : Fin n → E))
        (fun i => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul])
      beta_reduce at hc
      rw [GlobalTheory.LatticeIndex.det_single, _root_.mul_one, Matrix.det_one, _root_.one_mul] at hc
      exact hc
    · rw [map_pow, hk, one_pow]

private theorem valuation_beta_of_lattice_commensurable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (k : ℕ) (h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n)
    (h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La) {K : Type} [Field K] (io : c.F →+* K) (v0 : Valuation K (WithZero (Multiplicative ℤ)))
    (hint : ∀ x : K, IsIntegral ℤ x → v0 x ≤ 1) (hnat : v0 (k : K) = 1) (β : c.F)
    (hB : BetaIs (Dw := Dw) c Λ β) : v0 (io β) = 1 := by
  let w : Valuation c.F (WithZero (Multiplicative ℤ)) := v0.comap io
  have hwR : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r =>
    hint _ ((NumberField.RingOfIntegers.isIntegral_coe r).map io.toIntAlgHom)
  have hA : ∀ A : Submodule (𝓞 E) (Fin n → E), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) →
      ∀ τ : E →+* ℂ, GlobalTheory.LatticeIndex.HasMax w (idealAt c A τ) 1 := by
    intro A hA1 hA2 τ
    let wτ : Valuation E (WithZero (Multiplicative ℤ)) := w.comap (embF c τ)
    have hwE : ∀ r : 𝓞 E, wτ (algebraMap (𝓞 E) E r) ≤ 1 := fun r =>
      hint _ ((NumberField.RingOfIntegers.isIntegral_coe r).map (io.comp (embF c τ)).toIntAlgHom)
    have hkE : wτ (k : E) = 1 := by
      simp only [wτ, w, Valuation.comap_apply, map_natCast]
      exact hnat
    have hm := detSet_max wτ hwE A hkE hA1 hA2
    unfold idealAt
    refine GlobalTheory.LatticeIndex.hasMax_span hwR ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      exact hm.1 d hd
    · obtain ⟨d, hd, hd1⟩ := hm.2
      exact ⟨_, ⟨d, hd, rfl⟩, hd1⟩
  have hprod : ∀ A : Submodule (𝓞 E) (Fin n → E), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) →
      GlobalTheory.LatticeIndex.HasMax w (∏ τ : E →+* ℂ, idealAt c A τ ^ Dw.mult τ) 1 := by
    intro A hA1 hA2
    have := GlobalTheory.LatticeIndex.hasMax_prod hwR Finset.univ (fun τ => idealAt c A τ ^ Dw.mult τ) (fun _ => 1)
      (fun τ => by simpa using (hA A hA1 hA2 τ).pow hwR (Dw.mult τ))
    simpa using this
  have memLn : ∀ x, x ∈ Λ.Ln ↔ x ∈ Λ.La ∧ x ∈ stdLat E n := fun x => by
    unfold GenLat.Ln
    exact Submodule.mem_inf
  have hLa := hprod Λ.La h1 h2
  have hLn := hprod Λ.Ln (fun v hv => nsmul_mem ((memLn v).1 hv).2 k)
    (fun v hv => (memLn _).2 ⟨h2 v hv, nsmul_mem hv k⟩)
  have hβ : GlobalTheory.LatticeIndex.HasMax w (𝓞 c.F ∙ β) (w β) :=
    GlobalTheory.LatticeIndex.hasMax_span hwR (by rintro y rfl; exact le_rfl) ⟨β, Set.mem_singleton β, rfl⟩
  have hm := hβ.mul hLa
  unfold BetaIs at hB
  rw [hB] at hm
  have hu := hm.unique hLn
  rw [_root_.mul_one] at hu
  exact hu

end

theorem trivAt_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → Λ.TrivAt ℓ → (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ = (Λ.mIdx N (Dw.p + Dw.q)).factorization ℓ ∧ Λ.mIdx N (Dw.p + Dw.q) ≠ 0 ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), ¬ IsUnit (ℓ : T.V) → (∀ β : c.F, β ≠ 0 → BetaIs (Dw := Dw) c Λ β → vV T.V (io β) = 0) ∧ ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → MvPolynomial.map io P ∈ FFV (Dw := Dw) T w n := by
  intro E _ _ _ H Dw l c n Λ N M ℓ _ hL hl hT
  obtain ⟨k, hk, hk1, hk2⟩ := hT
  have h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n := fun v hv => nsmul_mem_of_le hk1 hv
  have h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La := fun v hv => nsmul_mem_of_le hk2 hv
  obtain ⟨hidx, hne⟩ := index_part Λ N M ℓ k hL hl hk h1 (Dw.p + Dw.q)
  refine ⟨hidx, hne, fun T io hlT => ⟨?_, ?_⟩⟩
  · intro β _ hB
    have key : valV T.V (io β) = 1 := by
      have hint : ∀ x : T.Fr, IsIntegral ℤ x → valV T.V x ≤ 1 := fun x hx => GlobalTheory.LatticeIndex.valV_integral T hx
      have hnat := GlobalTheory.LatticeIndex.valV_nat T hk hlT
      unfold valV at hint hnat ⊢
      refine valuation_beta_of_lattice_commensurable c Λ k h1 h2 io _ ?_ ?_ β hB
      · intro x hx
        refine hint x ?_
        convert hx
        all_goals first
          | rfl
          | exact rfl
          | exact Subsingleton.elim _ _
          | (apply Algebra.algebra_ext; intro r; simp)
      · first
          | exact hnat
          | convert hnat using 2
    unfold vV
    rw [key]
    simp
  · intro w P hP
    have hunit : IsUnit (k : T.V) := by
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hk).map (Int.castRingHom T.V)
      have hab' : a * (k : T.V) + b * (ℓ : T.V) = 1 := by simpa using hab
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab' with h | h
      · exact isUnit_of_mul_isUnit_right h
      · exact absurd (isUnit_of_mul_isUnit_right h) hlT
    have hunitary : ∀ i j : Fin n, ∑ b, IsCMField.complexConj E ((1 : Matrix (Fin n) (Fin n) E) b i) *
        (1 : Matrix (Fin n) (Fin n) E) b j = if i = j then 1 else 0 := by
      intro i j
      rw [Finset.sum_eq_single i]
      · simp [Matrix.one_apply]
      · intro b _ hb
        simp [Matrix.one_apply_ne hb]
      · intro h
        exact absurd (Finset.mem_univ i) h
    obtain ⟨hmem, hone, -⟩ := GlobalTheory.PushIntegral.map_pushL_mem_FFV E H Dw l c n Λ w P hP T io k 1 hunit hunitary
      (fun v hv => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul]; exact h1 v hv)
    rwa [hone] at hmem

end GlobalTheory.TrivLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MaximalIdealFormalPointsFormModule
section
set_option autoImplicit false
noncomputable section
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.PlaceInt.FormalPts

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {d : ℕ}

def SmallPt {n : ℕ} (x : Pt V n d) : Prop := ∀ i, MvPowerSeries.constantCoeff (x i) ∈ maximalIdeal V

def subPt {m n : ℕ} (a : Fin m → Pt V n d) (p : Pt V m d) : Pt V n d := fun i => evV a (p i)

theorem small_one {n : ℕ} {x : Pt V n d} (hx : SmallPt x) : ∀ j, SmallPt (![x] j) := by
  intro j
  fin_cases j
  simpa using hx

theorem small_two {n : ℕ} {x y : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) : ∀ j, SmallPt (![x, y] j) := by
  intro j
  fin_cases j
  · simpa using hx
  · simpa using hy

theorem small_three {n : ℕ} {x y z : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) (hz : SmallPt z) :
    ∀ j, SmallPt (![x, y, z] j) := by
  intro j
  fin_cases j
  · simpa using hx
  · simpa using hy
  · simpa using hz

variable [IsAdicComplete (maximalIdeal V) V] [CharZero V]

theorem small_evV {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (f : PS V m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (evV a f) ∈ maximalIdeal V := by
  have S := evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  exact S.2.1 f (by rw [hf]; exact zero_mem _)

theorem evV_ev {l m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (b : Fin l → Pt V m d)
    (hb : ∀ j, GP (b j)) (f : PS V l d) : evV a (ev b f) = evV (fun j => subPt a (b j)) f := by
  have hb' : ∀ p : Fin l × Fin d, MvPowerSeries.constantCoeff (b p.1 p.2) ∈ maximalIdeal V := fun p => by
    rw [hb p.1 p.2]
    exact zero_mem _
  have S := evC_spec V (Fin l × Fin d) (Fin m × Fin d) (Fin n × Fin d) (fun p => b p.1 p.2) hb'
  have e1 : ev b f = evC (fun p : Fin l × Fin d => b p.1 p.2) f := (S.2.2.1 (fun p => hb p.1 p.2) f).symm
  rw [e1]
  exact S.2.2.2 (fun p => a p.1 p.2) (fun p => ha p.1 p.2) f

theorem subPt_pt {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (j : Fin m) :
    subPt a (pt V d j) = a j := by
  funext i
  obtain ⟨⟨ψ, hX, hψ⟩, -⟩ :=
    evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  show evC (fun p : Fin m × Fin d => a p.1 p.2) (MvPowerSeries.X (j, i)) = a j i
  rw [hψ, hX]

theorem subPt_zero {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) :
    subPt a (0 : Pt V m d) = 0 := by
  funext i
  obtain ⟨⟨ψ, -, hψ⟩, -⟩ :=
    evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  show evC (fun p : Fin m × Fin d => a p.1 p.2) 0 = 0
  rw [hψ, map_zero]

theorem subPt_addOf {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (F : Fin d → PS V 2 d)
    (p q : Pt V m d) (hp : GP p) (hq : GP q) :
    subPt a (addOf F p q) = addV F (subPt a p) (subPt a q) := by
  funext i
  show evV a (ev ![p, q] (F i)) = evV ![subPt a p, subPt a q] (F i)
  rw [evV_ev a ha ![p, q] (pair_points_zero_constant hp hq) (F i)]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem subPt_comp1 {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (φ : Pt V 1 d)
    (p : Pt V m d) (hp : GP p) : subPt a (comp1 φ p) = compV φ (subPt a p) := by
  funext i
  show evV a (ev ![p] (φ i)) = evV ![subPt a p] (φ i)
  rw [evV_ev a ha ![p] (single_point_zero_constant hp) (φ i)]
  congr 1
  funext j
  fin_cases j
  rfl

variable (G : FGLaw V d) {n : ℕ}

theorem addV_comm {x y : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) : addV G.F x y = addV G.F y x := by
  funext i
  have h2 := small_two hx hy
  have g0 : GP (pt V (n := 2) d 0) := gp_pt 0
  have g1 : GP (pt V (n := 2) d 1) := gp_pt 1
  have key := congrArg (evV ![x, y]) (G.comm i)
  rw [evV_ev _ h2 _ (pair_points_zero_constant g1 g0)] at key
  refine key.symm.trans ?_
  show evV (fun j => subPt ![x, y] (![pt V (n := 2) d 1, pt V (n := 2) d 0] j)) (G.F i) = evV ![y, x] (G.F i)
  congr 1
  funext j
  fin_cases j
  · exact subPt_pt _ h2 1
  · exact subPt_pt _ h2 0

theorem addV_assoc {x y z : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) (hz : SmallPt z) :
    addV G.F (addV G.F x y) z = addV G.F x (addV G.F y z) := by
  funext i
  have h3 := small_three hx hy hz
  have g0 : GP (pt V (n := 3) d 0) := gp_pt 0
  have g1 : GP (pt V (n := 3) d 1) := gp_pt 1
  have g2 : GP (pt V (n := 3) d 2) := gp_pt 2
  have e0 : subPt ![x, y, z] (pt V (n := 3) d 0) = x := subPt_pt _ h3 0
  have e1 : subPt ![x, y, z] (pt V (n := 3) d 1) = y := subPt_pt _ h3 1
  have e2 : subPt ![x, y, z] (pt V (n := 3) d 2) = z := subPt_pt _ h3 2
  have key := congrArg (evV ![x, y, z]) (G.assoc i)
  have hl : evV ![x, y, z] (ev ![addOf G.F (pt V (n := 3) d 0) (pt V (n := 3) d 1), pt V (n := 3) d 2] (G.F i)) =
      addV G.F (addV G.F x y) z i := by
    rw [evV_ev _ h3 _ (pair_points_zero_constant (gp_addOf G.F G.const _ _ g0 g1) g2)]
    show evV _ (G.F i) = evV ![addV G.F x y, z] (G.F i)
    congr 1
    funext j
    fin_cases j
    · show subPt ![x, y, z] (addOf G.F (pt V (n := 3) d 0) (pt V (n := 3) d 1)) = addV G.F x y
      rw [subPt_addOf _ h3 _ _ _ g0 g1, e0, e1]
    · exact e2
  have hr : evV ![x, y, z] (ev ![pt V (n := 3) d 0, addOf G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)] (G.F i)) =
      addV G.F x (addV G.F y z) i := by
    rw [evV_ev _ h3 _ (pair_points_zero_constant g0 (gp_addOf G.F G.const _ _ g1 g2))]
    show evV _ (G.F i) = evV ![x, addV G.F y z] (G.F i)
    congr 1
    funext j
    fin_cases j
    · exact e0
    · show subPt ![x, y, z] (addOf G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)) = addV G.F y z
      rw [subPt_addOf _ h3 _ _ _ g1 g2, e1, e2]
  exact hl.symm.trans (key.trans hr)

theorem zero_addV {x : Pt V n d} (hx : SmallPt x) : addV G.F 0 x = x := by
  funext i
  have h1 := small_one hx
  have g0 : GP (pt V (n := 1) d 0) := gp_pt 0
  have e : subPt ![x] (pt V (n := 1) d 0) = x := subPt_pt _ h1 0
  have key := congrArg (evV ![x]) (G.unit i)
  rw [evV_ev _ h1 _ (pair_points_zero_constant gp_zero₂ g0)] at key
  refine Eq.trans ?_ (key.trans (congrFun e i))
  show evV ![0, x] (G.F i) = _
  congr 1
  funext j
  fin_cases j
  · exact (subPt_zero _ h1).symm
  · exact e.symm

theorem addV_zero {x : Pt V n d} (hx : SmallPt x) : addV G.F x 0 = x := by
  have h0 : SmallPt (0 : Pt V n d) := fun i => by
    show MvPowerSeries.constantCoeff (0 : PS V n d) ∈ maximalIdeal V
    rw [map_zero]
    exact zero_mem _
  rw [addV_comm G hx h0]
  exact zero_addV G hx

variable {O : Type} [CommRing O] {G} (A : OAct O G)

theorem act_addV (a : O) {x y : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) :
    compV (A.act a) (addV G.F x y) = addV G.F (compV (A.act a) x) (compV (A.act a) y) := by
  have h2 := small_two hx hy
  have g0 : GP (pt V (n := 2) d 0) := gp_pt 0
  have g1 : GP (pt V (n := 2) d 1) := gp_pt 1
  have e0 : subPt ![x, y] (pt V (n := 2) d 0) = x := subPt_pt _ h2 0
  have e1 : subPt ![x, y] (pt V (n := 2) d 1) = y := subPt_pt _ h2 1
  have hφ : GP (A.act a) := A.const a
  have key := congrArg (subPt ![x, y]) (A.hom a)
  unfold FGLaw.add at key
  rw [subPt_comp1 _ h2 _ _ (gp_addOf _ G.const _ _ g0 g1), subPt_addOf _ h2 _ _ _ g0 g1,
    subPt_addOf _ h2 _ _ _ (gp_comp1 _ _ hφ g0) (gp_comp1 _ _ hφ g1), subPt_comp1 _ h2 _ _ g0,
    subPt_comp1 _ h2 _ _ g1, e0, e1] at key
  exact key

theorem add_actV (a b : O) {x : Pt V n d} (hx : SmallPt x) :
    compV (A.act (a + b)) x = addV G.F (compV (A.act a) x) (compV (A.act b) x) := by
  show subPt ![x] (A.act (a + b)) = addV G.F (subPt ![x] (A.act a)) (subPt ![x] (A.act b))
  rw [A.add_act a b]
  unfold FGLaw.add
  exact subPt_addOf _ (small_one hx) _ _ _ (A.const a) (A.const b)

theorem mul_actV (a b : O) {x : Pt V n d} (hx : SmallPt x) :
    compV (A.act (a * b)) x = compV (A.act a) (compV (A.act b) x) := by
  show subPt ![x] (A.act (a * b)) = compV (A.act a) (subPt ![x] (A.act b))
  rw [A.mul_act a b]
  exact subPt_comp1 _ (small_one hx) _ _ (A.const b)

theorem one_actV {x : Pt V n d} (hx : SmallPt x) : compV (A.act 1) x = x := by
  show subPt ![x] (A.act 1) = x
  rw [A.one_act]
  exact subPt_pt _ (small_one hx) 0

theorem zero_actV {x : Pt V n d} (hx : SmallPt x) : compV (A.act 0) x = 0 := by
  show subPt ![x] (A.act 0) = 0
  rw [GlobalTheory.FourierChainCompare.act_zero A]
  exact subPt_zero _ (small_one hx)

theorem addV_neg_actV {x : Pt V n d} (hx : SmallPt x) : addV G.F x (compV (A.act (-1)) x) = 0 := by
  have h := add_actV A 1 (-1) hx
  rw [one_actV A hx, add_neg_cancel, zero_actV A hx] at h
  exact h.symm

end GlobalTheory.PlaceInt.FormalPts

namespace GlobalTheory.PlaceInt
open FormalPts

theorem smallPts_module : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (x y z : Pt V n d), (∀ i, MvPowerSeries.constantCoeff (x i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (y i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (z i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (addV B.G.F x y i) ∈ maximalIdeal V) ∧ addV B.G.F x y = addV B.G.F y x ∧ addV B.G.F (addV B.G.F x y) z = addV B.G.F x (addV B.G.F y z) ∧ addV B.G.F x 0 = x ∧ addV B.G.F x (compV (B.A.act (-1)) x) = 0 ∧ compV (B.A.act 1) x = x ∧ compV (B.A.act 0) x = 0 ∧ ∀ a b : O, (∀ i, MvPowerSeries.constantCoeff (compV (B.A.act a) x i) ∈ maximalIdeal V) ∧ compV (B.A.act a) (addV B.G.F x y) = addV B.G.F (compV (B.A.act a) x) (compV (B.A.act a) y) ∧ compV (B.A.act (a + b)) x = addV B.G.F (compV (B.A.act a) x) (compV (B.A.act b) x) ∧ compV (B.A.act (a * b)) x = compV (B.A.act a) (compV (B.A.act b) x) := by
  intro V _ _ _ _ _ d O _ _ B n x y z hx hy hz
  refine ⟨fun i => small_evV ![x, y] (small_two hx hy) (B.G.F i) (B.G.const i), addV_comm B.G hx hy,
    addV_assoc B.G hx hy hz, addV_zero B.G hx, addV_neg_actV B.A hx, one_actV B.A hx, zero_actV B.A hx,
    fun a b => ⟨fun i => small_evV ![x] (small_one hx) (B.A.act a i) (B.A.const a i), act_addV B.A a hx hy,
      add_actV B.A a b hx, mul_actV B.A a b hx⟩⟩

end GlobalTheory.PlaceInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpecStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ τ ρ : Type) [Finite σ] [Finite τ] [Finite ρ] (a : σ → MvPowerSeries τ V), (∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) → (∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, (∀ j, ψ (MvPowerSeries.X j) = a j) ∧ ∀ f, evC a f = ψ f) ∧ (∀ f, MvPowerSeries.constantCoeff f ∈ maximalIdeal V → MvPowerSeries.constantCoeff (evC a f) ∈ maximalIdeal V) ∧ ((∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f, evC a f = MvPowerSeries.subst a f) ∧ ∀ b : τ → MvPowerSeries ρ V, (∀ j, MvPowerSeries.constantCoeff (b j) ∈ maximalIdeal V) → ∀ f, evC b (evC a f) = evC (fun j => evC b (a j)) f := by
  first | exact @GlobalTheory.PlaceInt.evC_spec | exact GlobalTheory.PlaceInt.evC_spec | (intros; apply GlobalTheory.PlaceInt.evC_spec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslationsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedPullback_commutes_symmetric_translations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (β : 𝓞 E) (N k k' : ℕ), β * H.bar β = (N : 𝓞 E) → k' = k * N → Odd k' → ∀ (b b' : (ptO Xo x ⟶ Xo.univ.t.G)), b' ≫ Xo.univ.t.act.act β = b → b' ^ k' = 1 → ∀ (F G : SecN Xo x k) (F' G' : SecN Xo x k'), Moves Xo b F G → Pulls Xo β F F' → Pulls Xo β G G' → Moves Xo b' F' G' := by
  first | exact @GlobalTheory.PlaceInt.moves_of_pulls | exact GlobalTheory.PlaceInt.moves_of_pulls | (intros; apply GlobalTheory.PlaceInt.moves_of_pulls <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SectionRegularOnModelOfNuNonnegStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_regular_on_model_of_nu_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ (k : ℕ) (F₀ : SecN Xo (xOf y) k) (hh : SecN Xo xF k), 1 ≤ k → IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((k : ℕ) : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F₀ hh → (∀ σ s, SecTieF I P F xF k σ hh → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) → ∃ σ, ReciprocityTheory.ChartRestriction.G.PullbackSections.SecTie I k F₀ σ := by
  first | exact @GlobalTheory.NuRegular.main | exact GlobalTheory.NuRegular.main | (intros; apply GlobalTheory.NuRegular.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_rational_over_finite_extension_level_structure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (M : ℕ), 0 < M → (∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ AllRat Xo (spMap (algebraMap K L) ≫ x) M) ∧ (AllRat Xo x M → (∀ (L : Type) [Field L] (ψ : K →+* L), AllRat Xo (spMap ψ ≫ x) M) ∧ ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev a = 1 ↔ Dw.ModN M a) ∧ ∀ w : (ptO Xo x ⟶ Xo.univ.t.G), w ^ M = 1 → ∃ a, ev a = w) := by
  first | exact @GlobalTheory.torsion_rational_over_finite_extension | exact GlobalTheory.torsion_rational_over_finite_extension | (intros; apply GlobalTheory.torsion_rational_over_finite_extension <;> assumption)
end

